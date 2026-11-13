#!/usr/bin/env bash
# Complete this worktree's own Mathlib package tree at its resolved head.
#
# Why: Lake deletes a module's .olean and sibling build files when it rebuilds
# the module (src/lean/lake/Lake/Build/Module.lean:744-753,
# Module.clearOutputArtifacts). With the per-worktree package layout
# (lean-categories#143), this workspace's `.lake/packages` is this worktree's
# own tree, so a rebuild here removes build files that only this worktree's
# build reads. The Mathlib cache tool still skips a module whose .trace exists
# (Cache/IO.lean:487, ModuleHashMap.filterNeedsDecompression), so once this
# worktree's head has moved and its tree holds stale traces, `lake exe cache
# get` leaves the gap in place and Lake rebuilds the missing modules from
# source inside this worktree's tree.
#
# What this does: remove every module's trace in this worktree's own package
# tree, then `lake exe cache get` decompresses all of them from the shared
# download cache (~/.cache/mathlib), refreshing the stale ones as well as the
# missing ones. After it runs, this worktree's tree is complete at its head
# and `lake build` links against it without deleting anything. No other
# worktree's tree is touched: each worktree runs its own copy of this script
# against its own `.lake/packages`.
set -euo pipefail
cd "$(dirname "$0")/.."

# This workspace's own mathlib package directory: Lake's default packagesDir,
# relative to this worktree's root.
M=".lake/packages/mathlib"

# The modules at this worktree's head whose .olean is missing from its tree.
GAP=$(mktemp)
for f in $(git -C "$M" ls-tree -r --name-only HEAD -- Mathlib | grep '\.lean$'); do
  o="$M/.lake/build/lib/lean/${f%.lean}.olean"
  [ -f "$o" ] || echo "$f" >> "$GAP"
done
echo "worktree gap: $(wc -l < "$GAP") modules"

# Remove every module's trace in this worktree's tree so the cache tool
# decompresses all of them (refreshing the stale ones too), not just the
# missing ones: a head move changes modules whose .olean is present but
# stale, and the trace-based skip leaves them unfilled, so Lake rebuilds
# them from source inside this worktree's tree.
for f in $(git -C "$M" ls-tree -r --name-only HEAD -- Mathlib | grep '\.lean$'); do
  m="${f%.lean}"
  rm -f "$M/.lake/build/lib/lean/$m.trace" "$M/.lake/build/lib/lean/$m.trace.hash"
done

# Decompress the build files from the shared download cache.
lake exe cache get

# Verify this worktree's tree is complete.
MISS=0
while read -r f; do
  o="$M/.lake/build/lib/lean/${f%.lean}.olean"
  [ -f "$o" ] || MISS=$((MISS+1))
done < "$GAP"
rm -f "$GAP"
echo "still missing: $MISS"
[ "$MISS" -eq 0 ]
