# One Mathlib build per revision on the VM (lean-categories#148)

Every worktree resolves its own `.lake/packages` (lean-categories#143), so every worktree also
carries its own copy of the Mathlib build: `lake exe cache get` decompresses Mathlib's cached
`.olean` files into the tree of the worktree that runs it. Four chats on the team VM therefore hold
four copies of the same 6.8 GB, and the VM's single disk does not have the room
(lean-categories#148: the VM lost its platform link after each time the Lean chats ran their
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
nobody edits: one Mathlib checkout's build outputs are a pure function of the Mathlib revision and
the Lean toolchain.

## Mechanism

`scripts/cache-get.sh` keeps one build tree per (Mathlib revision, Lean toolchain) in a store, and
gives each worktree a tree of **hardlinks** into it:

```
<git-common-dir>/lake-build-store/<mathlib-rev>-<toolchain>/lib/lean   one copy of the bytes
<worktree>/.lake/packages/mathlib/.lake/build/lib/lean                 that worktree's links
```

The store lives in the repository's own `git` directory, which is the one location all of its
worktrees share, so it is repository-owned build state rather than a global cache. `df` counts the
bytes once; `du` reports them once per inode. Per worktree this replaces 6.8G with inodes, so four
worktrees cost 6.8G in total instead of 27G.

A hardlink is safe here because neither tool writes a build file in place: Lake deletes a module's
outputs before rebuilding it (`src/lean/lake/Lake/Build/Module.lean:744-753`,
`Module.clearOutputArtifacts`), and the cache tool only writes files whose trace it has decided is
stale. Replacement — unlink, then create — drops one worktree's link and leaves the other bytes
alone, so one worktree's rebuild can no longer rewrite or remove what another reads, which was the
#143 defect. The script hands out an entry only after `lake build --no-build Mathlib` reports
`All targets up-to-date`, i.e. after Lake itself certifies that every trace in the tree matches the
sources at that revision; that is what keeps a second worktree from inheriting stale outputs.

## The order

A worktree moves to a new Mathlib head in three steps, and the first one must not fetch the cache:

```
just update    # MATHLIB_NO_CACHE_ON_UPDATE=1 lake update -- resolution only
just cache     # scripts/cache-get.sh -- link (or, for the first worktree, decompress) the tree
just build     # lake build -- runs the cache step first, so this alone is enough
```

Mathlib's own lakefile decompresses the cache itself at the end of `lake update`
(`lakefile.lean:193-197`, the `post_update` hook). That runs before this script
can share anything, writes a full 6.8G tree into the worktree that ran the
update, and four chats doing it at once is the disk exhaustion #148 reports.
`MATHLIB_NO_CACHE_ON_UPDATE=1` is Mathlib's own switch for it, and `just update`
sets it.

## Why not a mechanism Lake or the cache tool already provides

- **Lake's `packagesDir`** (the pre-#143 layout) names *one* package directory, hence one Mathlib
  checkout at one revision for every worktree that resolves it. Two worktrees cannot be at two
  heads, and two builds delete each other's `.olean` files: exactly what #143 removed.
- **Lake's artifact cache** (`lake cache get`, `LAKE_CACHE_DIR`, `--try-cache`) is keyed by input
  hash and does deduplicate content, but it restores artifacts by copying them: Lake creates no
  hard or symbolic links anywhere (`grep -rn 'createHardLink\|createSymlink' lake/Lake` finds
  nothing at Lean 4.36.0-rc2), so restoring still costs one full copy per worktree. It also only
  serves packages that publish mappings through Reservoir, and Mathlib publishes none — Mathlib's
  cache is `lake exe cache`, a separate tool.
- **The Mathlib cache tool** has no destination or linking option. `MATHLIB_CACHE_DIR`
  (`Cache/Main.lean:95`) names the *download* cache; decompression always targets the build
  directory of the package that runs it, which is the worktree's own tree under #143.

So the multi-revision store has to be ours; what it must not do is re-implement what these tools
already decide correctly, which is why the completeness check above is Lake's own.

## Acceptance

Recorded with the change in this commit's follow-up: four worktrees run `lake update`,
`scripts/cache-get.sh` and `lake build` at the same time, each ending `Build completed
successfully`, with the free space before, during and after.
