#!/usr/bin/env bash
# Complete the shared Mathlib package tree's build files at the current head.
#
# Why: Lake deletes a module's .olean and sibling build files when it rebuild
# the module (src/lean/lake/Lake/Build/Module.lean:744-753,
# Module.clearOutputArtifacts), and the lakefile's packagesDir points every
# worktree at one shared package tree, so one worktree's rebuild removes a
# build file another worktree's build reads. The Mathlib cache tool skips a
# module whose .trace exists (Cache/IO.lean:487,
# ModuleHashMap.filterNeedsDecompression), so once the head has moved and the
# tree holds stale traces, `lake exe cache get` leaves the gap in place and
# Lake rebuilds the missing modules from source inside the shared tree.
#
# What this does: remove the stale traces of exactly the modules whose .olean
# is missing, then `lake exe cache get` decompresses those modules' build
# files from the shared download cache (~/.cache/mathlib). After it runs, the
# tree is complete and `lake build` links against it without deleting
# anything.
set -euo pipefail
cd "$(dirname "$0")/.."

# The mathlib package directory, from the lakefile's packagesDir.
PKGS=$(sed -n 's/^packagesDir *= *"\([^"]*\)".*/\1/p' lakefile.toml)
M="$PKGS/mathlib"

# The modules at the head whose .olean is missing from the tree.
GAP=$(mktemp)
for f in $(git -C "$M" ls-tree -r --name-only HEAD -- Mathlib | grep '\.lean$'); do
  o="$M/.lake/build/lib/lean/${f%.lean}.olean"
  [ -f "$o" ] || echo "$f" >> "$GAP"
done
echo "store gap: $(wc -l < "$GAP") modules"

# Remove the stale traces so the cache tool no longer skips them.
while read -r f; do
  m="${f%.lean}"
  rm -f "$M/.lake/build/lib/lean/$m.trace" "$M/.lake/build/lib/lean/$m.trace.hash"
done < "$GAP"

# Decompress the missing build files from the shared download cache.
lake exe cache get

# Verify the tree is complete.
MISS=0
while read -r f; do
  o="$M/.lake/build/lib/lean/${f%.lean}.olean"
  [ -f "$o" ] || MISS=$((MISS+1))
done < "$GAP"
rm -f "$GAP"
echo "still missing: $MISS"
[ "$MISS" -eq 0 ]
