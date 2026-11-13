#!/usr/bin/env bash
# Give this worktree a complete Mathlib build at its resolved head, keeping one
# copy of Mathlib's build tree per revision for every worktree of this
# repository (lean-categories#148), not one per worktree.
#
# Why per worktree was wrong. Lake materializes a package in the workspace's own
# `.lake/packages` (lean-categories#143), so `lake exe cache get` decompresses
# Mathlib's cached build into the tree of whichever worktree runs it: 6.8 GB of
# `.olean` files (130951 files, 8725 `.olean`) per worktree, and four chats on
# the team VM hold four copies of the same bytes on one 248 GB disk with 16 GB
# free. See `docs/mathlib-build-store.md` for the measurement and for why Lake's
# `packagesDir` and artifact cache and Mathlib's own cache tool cannot remove the
# duplication.
#
# Why traces had to be cleared. Lake deletes a module's .olean and sibling build
# files when it rebuilds the module (src/lean/lake/Lake/Build/Module.lean:744-753,
# Module.clearOutputArtifacts). The Mathlib cache tool skips a module whose .trace
# exists (Cache/IO.lean:472-490, ModuleHashMap.filterNeedsDecompression), so once
# a worktree's head has moved and its tree holds stale traces, `lake exe cache
# get` leaves the gap in place and Lake rebuilds the missing modules from source
# inside that worktree's tree.
#
# What this does. A store keyed by Mathlib revision and Lean toolchain holds one
# build tree per key, and each worktree's `.lake/packages/mathlib/.lake/build/
# lib/lean` is a tree of hardlinks into it:
#
#   $STORE/<mathlib-rev>-<toolchain>/lib/lean    one copy of the bytes
#   .lake/packages/mathlib/.lake/build/lib/lean  this worktree's links
#
# $STORE is the repository's own git directory, which is the one place all of
# its worktrees share, so it is repository-owned build state rather than a global
# cache. `df` counts the bytes once. A hardlink is safe because neither tool
# writes a build file in place — Lake deletes a module's outputs before
# rebuilding it, and the cache tool writes only what it judged stale — so a
# rebuild replaces an inode and leaves every other worktree's bytes alone.
#
# A linked tree is never decompressed again, and that is the second half of the
# point. `lake exe cache get` judges a module stale by its own map, which is not
# Lake's judgement: on the tree measured for #148 it re-decompressed 403 modules
# that Lake considered up to date, and because the files were links shared with
# every other worktree, the rewritten oleans invalidated the traces of everything
# downstream and three worktrees then rebuilt 417 Mathlib modules from source.
# So `cache get` runs only on a worktree's own unshared tree, in the one case
# where that tree has to be filled; a worktree whose tree is the store's entry
# needs nothing fetched, and the script says so instead of re-fetching.
#
# A worktree is handed a store entry only after `lake build --no-build Mathlib`
# reports the tree up to date, i.e. after Lake itself certifies that every trace
# in it matches the sources at that revision. Without that check the store could
# hand a second worktree the stale outputs #143 was about.
#
# One revision is materialized once: a worktree that finds the entry missing
# decompresses it (holding a per-key lock) and every other worktree at that head
# links it instead, in seconds. Nothing else is serialized — each worktree still
# runs its own `lake update`, its own cache step and its own build, and no
# worktree's build waits for another's.
#
# Environment: MATHLIB_BUILD_STORE (default <git-common-dir>/lake-build-store),
# MATHLIB_BUILD_STORE_KEEP (entries to keep, default 2),
# MATHLIB_BUILD_STORE_MIN_FREE_GB (free space a decompression needs, default 7).
set -euo pipefail
cd "$(dirname "$0")/.."

# This workspace's own mathlib package directory: Lake's default packagesDir,
# relative to this worktree's root.
M=".lake/packages/mathlib"
BUILD="$M/.lake/build"
LINKED="$BUILD/lib/lean"
KEYFILE="$BUILD/mathlib-store-key"

if [ ! -d "$M" ]; then
  echo "cache-get.sh: no Mathlib checkout at $M; run 'lake update' first" >&2
  exit 1
fi

STORE="${MATHLIB_BUILD_STORE:-}"
if [ -z "$STORE" ]; then
  STORE="$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null \
    || echo .lake)/lake-build-store"
fi
KEEP="${MATHLIB_BUILD_STORE_KEEP:-2}"
MIN_FREE_GB="${MATHLIB_BUILD_STORE_MIN_FREE_GB:-7}"

# The modules at this worktree's head.
modules() {
  git -C "$M" ls-tree -r --name-only HEAD -- Mathlib | grep '\.lean$' || true
}

# How many of them have no .olean in this worktree's tree.
gap() {
  local n=0 f
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    [ -f "$LINKED/${f%.lean}.olean" ] || n=$((n + 1))
  done < <(modules)
  printf '%s\n' "$n"
}

# Remove every trace in this worktree's tree, so the cache tool decompresses all
# of it and cannot skip a module whose .olean is stale (see the header).
clear_traces() {
  local f m
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    m="${f%.lean}"
    rm -f "$LINKED/$m.trace" "$LINKED/$m.trace.hash"
  done < <(modules)
}

# Lake's own up-to-date check: every module's trace matches the sources at HEAD.
certified() {
  local out
  if out="$(lake build --no-build Mathlib 2>&1)"; then
    echo "mathlib build: Lake reports $out"
    return 0
  fi
  echo "mathlib build: Lake does not consider this tree up to date:" >&2
  printf '%s\n' "$out" | tail -n 5 >&2
  return 1
}

free_gb() {
  df -BG --output=avail "$STORE" 2>/dev/null | tail -n 1 | tr -dc '0-9'
}

# This worktree's own tree, completed as before #148, for the cases where the
# store cannot be used: a locally modified Mathlib checkout, or nowhere to put
# the store.
plain() {
  echo "mathlib build: completing this worktree's own tree ($M)"
  clear_traces
  lake exe cache get
}

# Complete this worktree's tree at its head, and put it in the store if the
# store has no entry for it yet.
cold() {
  local avail n tmp
  avail="$(free_gb)"
  if [ "${avail:-0}" -lt "$MIN_FREE_GB" ]; then
    echo "mathlib build: only ${avail:-0}G free; decompressing Mathlib needs about 7G" >&2
    echo "mathlib build: free space, or set MATHLIB_BUILD_STORE_MIN_FREE_GB" >&2
    exit 1
  fi
  echo "mathlib build: $KEY has no entry in $STORE; decompressing Mathlib's cache here"
  clear_traces
  lake exe cache get
  n="$(gap)"
  if [ "$n" -ne 0 ]; then
    echo "mathlib build: the cache does not cover $n module(s) at $REV; not seeding $ENTRY" >&2
    return 0
  fi
  if ! certified; then
    echo "mathlib build: not seeding $ENTRY from an uncertified tree" >&2
    return 0
  fi
  # Link the entry beside its final name and rename it into place, so no other
  # worktree can read a half-written entry.
  tmp="$STORE/.$KEY.tmp.$$"
  rm -rf "$tmp"
  mkdir -p "$tmp/lib"
  cp -al "$LINKED" "$tmp/lib/lean"
  rm -rf "$ENTRY"
  mv "$tmp" "$ENTRY"
  touch "$ENTRY/.complete"
  printf '%s\n' "$KEY" > "$KEYFILE"
  echo "mathlib build: seeded $ENTRY ($(du -sh "$ENTRY" | cut -f1))"
}

# Replace this worktree's tree with hardlinks into the store's entry.
relink() {
  echo "mathlib build: linking this worktree's tree to $ENTRY (nothing to fetch)"
  rm -rf "$LINKED"
  mkdir -p "$BUILD/lib"
  cp -al "$ENTRY/lib/lean" "$LINKED"
  printf '%s\n' "$KEY" > "$KEYFILE"
}

# Whether this worktree's tree already is the store entry's inodes.
linked() {
  local a b
  a="$(stat -c '%d:%i' "$LINKED/Mathlib.olean" 2>/dev/null || echo none)"
  b="$(stat -c '%d:%i' "$ENTRY/lib/lean/Mathlib.olean" 2>/dev/null || echo none)"
  [ "$a" = "$b" ] && [ "$a" != none ]
}

# Drop store entries beyond the newest $KEEP that no other worktree is filling.
# Removing an entry only unlinks the store's links; worktrees already linked to
# it keep their bytes, so this can never break a running build.
prune() {
  local d k kept=0
  for d in $(ls -1dt "$STORE"/*/ 2>/dev/null); do
    k="$(basename "$d")"
    kept=$((kept + 1))
    [ "$kept" -le "$KEEP" ] && continue
    if flock -n "$STORE/.$k.lock" rm -rf "$d" 2>/dev/null; then
      echo "mathlib build: pruned store entry $k (keeping $KEEP)"
    fi
  done
}

REV="$(git -C "$M" rev-parse HEAD)"
TOOL="$(tr -d '\n' < lean-toolchain | tr -cs 'A-Za-z0-9._-' '_')"
KEY="$REV-$TOOL"
ENTRY="$STORE/$KEY"

# A locally modified Mathlib checkout is not described by its revision, so it can
# neither take its tree from the store nor seed it.
if [ -n "$(git -C "$M" status --porcelain -- Mathlib 2>/dev/null)" ]; then
  echo "mathlib build: $M has local modifications; staying out of the shared store"
  plain
  exit 0
fi

if ! mkdir -p "$STORE" 2>/dev/null; then
  echo "mathlib build: cannot create $STORE; completing this worktree's own tree only"
  plain
  exit 0
fi

GOT=0
exec 9>"$STORE/.$KEY.lock"
if ! flock -n 9; then
  echo "mathlib build: another worktree is completing $KEY; waiting for it"
  flock 9
fi
if [ -f "$ENTRY/.complete" ]; then
  if [ "$(cat "$KEYFILE" 2>/dev/null || true)" = "$KEY" ] && [ "$(gap)" -eq 0 ] && linked; then
    echo "mathlib build: this worktree's tree is already linked from $ENTRY, nothing to fetch"
  else
    relink
  fi
  touch "$ENTRY"
else
  # Nothing to link to: fill this worktree's own tree, certify it, seed the store.
  cold
  GOT=1
fi
exec 9>&-

if [ "$GOT" -eq 1 ]; then
  echo "mathlib build: $REV, toolchain $TOOL, tree filled and seeded from the cache"
fi
MISS="$(gap)"
echo "mathlib build: $REV, toolchain $TOOL, $MISS module(s) without an .olean"
prune
[ "$MISS" -eq 0 ]
