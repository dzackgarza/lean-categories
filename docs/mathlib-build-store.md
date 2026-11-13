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
used to cost -- as long as the worktrees are on the same revision. Moving one of them to a new
Mathlib head seeds a second 6.7G entry for as long as the old head is needed, so the store also has
to forget: see *An entry is kept only while a worktree names it*, below.

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

### An entry is kept only while a worktree names it

The store used to keep the newest `MATHLIB_BUILD_STORE_KEEP` (default 2) entries of each package. That
number is not a property of anything, and it did not bound the store: on 2026-11-13 it held the head
one worktree was on, the head it had left, and the revision a third worktree had resolved, and the
VM's one disk stood at 9 GB free with three Lean chats stopped (lean-categories#149). An entry lives
now while some worktree of the repository -- `git worktree list`, every one of them, not the newest
two -- names that revision in its `lake-manifest.json`. Anything else in the store is dropped, of
every package, including ones this workspace does not resolve at all, and so is an unfinished
`<rev>-<toolchain>.tmp.<pid>` seed whose process is gone. `MATHLIB_BUILD_STORE_KEEP` is gone with the
rule that needed it.

Nothing is deleted out from under a build. Two things put an entry in use, and both are read from
`/proc` before any removal:

- **A process holds a path inside the entry.** That is another worktree's `cp -al`, a `du`, or a seed
  being written. This has to be read from `/proc/<pid>/fd` *and* `/proc/<pid>/maps`, because Lean
  maps an `.olean` and closes the descriptor it opened it with, so the descriptors alone would miss a
  build that is in fact reading the file.
- **A `lake`, `lean` or `leanc` process is working inside a worktree whose tree is that entry's
  inodes** — the same inode test that decides whether a tree is linked. That is a build that started
  before this run and has not finished, in a worktree whose manifest has since moved to another head;
  it keeps its entry. Any process holding a path under a worktree's `.lake` counts the same way, so a
  `lake update` whose manifest is momentarily half-written cannot be mistaken for a worktree that
  names nothing.

Removal also takes the entry's own per-key lock, so it cannot land inside another worktree's `fill`
or `relink` of that key; an entry whose lock is held is skipped with a message. The eviction runs
twice per invocation: once after every package with an entry is linked and before anything is
decompressed -- which is what makes the space ordering work, since the head a worktree has left is
named by no manifest any more and its 6.7 GB are released by the `unlink_tree` of the fill instead of
being held beside the next 6.7 GB -- and once at the end, so the store is clean when the run returns.

### What a stale worktree pins

Removing an entry only unlinks the store's names for its inodes. A hardlinked file gives its space
back when its last link goes, so an entry that is dropped frees nothing while a worktree still has
that tree linked: the space arrives when the last linked worktree relinks (which `fill` does by
dropping the tree before decompressing) or when that tree is deleted. A worktree that is registered
but never relinks -- one left behind by a stopped chat -- keeps its copy of the bytes to itself, and
no amount of eviction reclaims it; `du -sh .lake/packages` in that worktree shows it. The same
worktree's `lake-manifest.json` also keeps alive the entry it names. Both are consequences of what
the store is: a set of names for bytes that the worktrees own, not a cache it can clear on its own.

A decompression refuses to start with less than `MATHLIB_BUILD_STORE_MIN_FREE_GB` (default 7) free.

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

## Acceptance

Measured 2026-11-13 on the team VM (4 cores, 15G RAM, one 248G disk). Four **fresh**
worktrees of the same commit, each running `just update`, `scripts/cache-get.sh` and
`lake build` at the same time, started 11:29:33Z:

| Worktree | `just update` | cache step | `lake build` | Pipeline ends |
| --- | --- | --- | --- | --- |
| wt1 | 1m49s | 21s | 6m28s | 11:37:50Z, `Build completed successfully (8338 jobs)` |
| wt2 | 2m18s | 23s | 6m57s | 11:38:48Z, `Build completed successfully (8338 jobs)` |
| wt3 | 4m19s | 25s | 5m36s | 11:39:28Z, `Build completed successfully (8338 jobs)` |
| wt4 | 3m12s | 20s | 6m29s | 11:39:14Z, `Build completed successfully (8338 jobs)` |

Every one of them linked all ten packages ("nothing to fetch"), certified all ten
(`All targets up-to-date`), and rebuilt **no** Mathlib module and **no** module of any
dependency — the only thing `lake build` compiled was the repository's own 8338-job
target graph.

| Quantity | Value |
| --- | --- |
| `df -h /` before | 16G available (15.6G exact) |
| `df -h /` during | never below 14G (13.xG exact) — the 10G floor was never approached |
| `df -h /` after | 14G available (13.0G exact) |
| New bytes per worktree | about 0.65G — 433M of `LeanCategories` build tree, 220M of package sources |
| `du -sh .git/lake-build-store` | 7.2G for ten packages: 6.7G Mathlib, 0.5G the rest |
| `du -sh .lake/packages` in a linked worktree | 7.4G, of which 6.9G are the store's inodes |

The 1.7G Mathlib *download* cache in `~/.cache/mathlib` was removed before the run to
give it headroom; the store holds the decompressed trees, so nothing that run did
depended on the cache. A later `lake exe cache get` re-downloads what it needs.

Sizing, if the whole thing has to be repeated on a colder disk: the first worktree at
a new revision pays a 6.7G decompression (about 40 s, plus the download), and every
worktree after it pays 0.65G.

## Acceptance: three Mathlib head moves (lean-categories#149)

Measured 2026-11-13 on the same VM, with the eviction in place and the main checkout as the only
worktree holding a Mathlib tree. Mathlib's master head was `7bcc5e95` all afternoon, so `rev =
"master"` would have resolved to the same revision three times and moved nothing; each run pinned the
requirement to the commit it was meant to move to, and `just update` resolved that head, which is what
it does when master moves on its own.

| Move | Mathlib head | run | free before (bytes) | free after (bytes) | change |
| --- | --- | --- | --- | --- | --- |
| — | `7bcc5e95`, before | — | 16623714304 (16G) | — | — |
| 1 | `3d487513` (08:50Z) | drop 6.3G entry, 7657 `.ltar`, decompress 18800 ms | 16623636480 | 16241729536 | −364 MiB |
| 2 | `d9aae7cd` (11:38Z) | drop 6.3G entry, decompress, BrauerGroup refilled | 16241635328 | 16239517696 | −2.0 MiB |
| 3 | `7bcc5e95` (master) | back to the master head, same way | 16239480832 | 16237748224 | −1.7 MiB |

The store was 7.2G with **exactly one** Mathlib entry at every one of those measurements, before and
after each move: the 6.3G entry a move left behind was dropped before the next head was decompressed.
What the three moves cost in total is 367 MiB, all of it `.ltar` files in `~/.cache/mathlib` (458M to
824M) and bookkeeping; the build trees replaced each other. Before this change the same three moves
would have left 19G of Mathlib entries in the store and taken the disk to under zero.

Two costs the runs show and this change does not remove. A head move decompresses Mathlib twice: the
certification step finds `BrauerGroup` stale -- an entry is keyed by its own revision and the
toolchain, not by the Mathlib revision it was compiled against -- and the refill path it triggers
refills every package rather than the ones that failed, so Mathlib is decompressed again. And an
entry's key is too coarse in the other direction as well: `batteries`, `aesop` and the rest are
unaffected by a Mathlib bump that does not move their own pins, which is why most of those entries are
linked rather than rebuilt, but a package that is stale for any reason costs a rebuild of itself the
first time a worktree links it.

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
