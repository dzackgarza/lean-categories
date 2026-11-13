# One build per package per revision on the VM (lean-categories#148)

Every worktree resolves its own `.lake/packages` (lean-categories#143), so every worktree also
carries its own copy of every package's build: `lake exe cache get` decompresses a package's cached
`.olean` files into the tree of the worktree that runs it. Four chats on the team VM therefore hold
four copies of the same bytes -- 6.8 GB of it Mathlib alone -- and the VM's single disk does not have
the room (lean-categories#148: the VM lost its platform link each time the Lean chats ran their
pipelines together).

## Measurement (2026-11-13, before the change)

| Quantity | Value |
| --- | --- |
| `df -h /` on the team VM | 248G size, 232G used, **16G available** (94 % used) |
| `du -sh .lake/packages` (the main checkout) | 7.3G |
| `du -sh .lake/packages/mathlib/.lake/build` | 6.8G — 130951 files, 8725 `.olean` |
| `du -sh .lake/packages/mathlib/Mathlib` (Mathlib's sources) | 118M |
| `du -sh ~/.cache/mathlib` (the shared download cache, 26370 `.ltar`) | 1.3G |
| `du -sh .lake` (all build state of one worktree) | 9.0G |

Four worktrees need 4 × 7.3G = 29G of `.lake/packages` alone, against 16G available, before this
repository's own 1.7G of build state is counted at all. The parts that are duplicated are the parts
nobody edits: a package's build outputs are a pure function of its own revision, the revisions of the
packages it imports, and the Lean toolchain.

## Mechanism

`scripts/cache-get.sh` keeps one build tree per (package, revision, Lean toolchain) in a store, and
gives each worktree a tree of **hardlinks** into it:

```
<git-common-dir>/lake-build-store/<package>/<rev>-<toolchain>/lib/lean   one copy of the bytes
<git-common-dir>/lake-build-store/<package>/<rev>-<toolchain>/ir         the cached IR, where there is one
<worktree>/.lake/packages/<package>/.lake/build/lib/lean                 that worktree's links
```

The store lives in the repository's own `git` directory, which is the one location all of its
worktrees share, so it is repository-owned build state rather than a global cache. `df` counts the
bytes once; `du` reports them once per inode. Per worktree this replaces about 7.3G with inodes, so
four worktrees cost one copy in total instead of four, and the store's own size is what one worktree
used to cost.

### Every package, not just Mathlib

Mathlib's build tree was never the whole problem. A fresh worktree also has to build `batteries`,
`aesop`, `Qq`, `importGraph`, `plausible`, `LeanSearchClient`, `proofwidgets`, `BrauerGroup`,
`checkdecls` and `Cli` -- about 480M of build tree -- and Lake schedules Mathlib's module traces from
those packages' `.olean` files. With them missing, a worktree whose *Mathlib* tree was already shared
still rebuilt 446-472 Mathlib modules; four of those at once is what the disk could not carry, at
16G free.

Most of those packages are already in Mathlib's cache. `Cache/IO.lean:24-46` (`isPartOfMathlibCache`)
lists the packages whose oleans Mathlib's cache carries -- Batteries, Aesop, Cli, ImportGraph,
LeanSearchClient, Plausible, Qq and ProofWidgets among them -- and `lake exe cache get <Module>`
decompresses one package's share of it (measured: `Batteries` in 2.5 s for 187 oleans, all eight
packages together in under 3 s, from the `.ltar` files `~/.cache/mathlib` already holds). So a
package is fetched, not compiled. The only packages that have to be compiled once are the ones no
cache covers -- `BrauerGroup` and `checkdecls` here -- and each is then shared like the rest.

### Traces are private, everything else is shared

Lake deletes a module's outputs before rebuilding the module
(`src/lean/lake/Lake/Build/Module.lean:744-753`, `Module.clearOutputArtifacts`), so a rebuild replaces
an inode and leaves every other worktree's bytes alone. It does **not** do that for the `.trace` file
beside them: Lake rewrites a trace in place, and a trace records the absolute path of the source file
it was built from (`Lake/Build/Module.lean:52-56`, the `inputFacet` trace). So a rebuild in one
worktree would rewrite the trace every other worktree reads to name a path that does not exist for
them, and that module -- and everything importing it -- would then be rebuilt everywhere the entry is
linked. The first version of this store was poisoned exactly that way: 2546 of its 8725 Mathlib traces
named a `.scratch/accept/wt6/...` path left behind by a previous run.

A linked tree therefore gets a copy of every `.trace` file and a hardlink for everything else: 8725
traces, about 9 MB per worktree, and no worktree can write into what another one reads. A rebuild is
then local to the worktree that does it, which is what the pre-#148 layout promised and #143 removed.

### An entry is only handed out certified

`lake build --no-build +<Module>` must report the package's modules up to date -- against the sources
at that revision and the packages they import -- before an entry is linked into another worktree, and
an entry is seeded only from a tree that check passed on. Without that check the store could hand a
second worktree the stale outputs #143 was about. If a worktree links the store and the check then
fails, the script drops the offending entries, refills every package from Mathlib's cache, and
refuses to seed anything unless the check passes.

### Order and locking

One revision of a package is materialized once, under a per-key lock; every other worktree at that
head links it in about a second (`cp -al` of 130k files). Nothing else is serialized: each worktree
still runs its own `lake update`, its own cache step and its own build, and no worktree's build waits
for another's. Inside one worktree the fill order is Mathlib's cache first and the packages built
after it second, because `lake build +<Module>` for a package needs the oleans it imports to be in
place.

The store keeps the newest `MATHLIB_BUILD_STORE_KEEP` entries (default 2) of each package and prunes
older ones; removing an entry only drops the store's links, so a worktree already linked to it keeps
its bytes. A decompression refuses to start with less than `MATHLIB_BUILD_STORE_MIN_FREE_GB` (default
7) free.

## The order

A worktree moves to a new Mathlib head in three steps, and the first one must not fetch the cache:

```
just update    # MATHLIB_NO_CACHE_ON_UPDATE=1 lake update -- resolution only
just cache     # scripts/cache-get.sh -- link (or, for the first worktree, decompress) the trees
just build     # lake build -- runs the cache step first, so this alone is enough
```

Mathlib's own lakefile decompresses the cache itself at the end of `lake update`
(`lakefile.lean:193-197`, the `post_update` hook). That runs before this script can share anything,
writes a full 6.8G tree into the worktree that ran the update, and four chats doing it at once is the
disk exhaustion #148 reports. `MATHLIB_NO_CACHE_ON_UPDATE=1` is Mathlib's own switch for it, and
`just update` sets it.

## Why not a mechanism Lake or the cache tool already provides

- **Lake's `packagesDir`** (the pre-#143 layout) names *one* package directory, hence one Mathlib
  checkout at one revision for every worktree that resolves it. Two worktrees cannot be at two
  heads, and two builds delete each other's `.olean` files: exactly what #143 removed.
- **Lake's artifact cache** (`lake cache get`, `LAKE_CACHE_DIR`, `--try-cache`) is keyed by input
  hash and does deduplicate content, but it restores artifacts by copying them: Lake creates no
  hard or symbolic links anywhere (`grep -rn 'createHardLink\|createSymlink' lake/Lake` finds
  nothing at Lean 4.36.0-rc2), so restoring still costs one full copy per worktree. It also only
  serves packages that publish mappings through Reservoir, and Mathlib publishes none -- Mathlib's
  cache is `lake exe cache`, a separate tool.
- **The Mathlib cache tool** has no destination or linking option. `MATHLIB_CACHE_DIR`
  (`Cache/Main.lean:95`) names the *download* cache; decompression always targets the build
  directory of the package that runs it, which is the worktree's own tree under #143.

So the multi-revision store has to be ours; what it must not do is re-implement what these tools
already decide correctly, which is why the completeness check above is Lake's own and why the oleans
come from Mathlib's cache wherever that cache covers the package.
