#!/usr/bin/env bash
# Give this worktree a complete build tree for every package it resolves -- Mathlib
# and each dependency in the manifest -- keeping one copy of each package's build
# per (package, revision, toolchain) for every worktree of this repository
# (lean-categories#148), not one per worktree.
#
# Why per worktree was wrong. Lake materializes a package in the workspace's own
# `.lake/packages` (lean-categories#143), so `lake exe cache get` decompresses
# Mathlib's cached build into the tree of whichever worktree runs it: 6.8 GB of
# `.olean` files (130951 files, 8725 `.olean`) per worktree, and four chats on the
# team VM hold four copies of the same bytes on one 248 GB disk with 16 GB free.
# See `docs/mathlib-build-store.md` for the measurement and for why Lake's
# `packagesDir` and artifact cache and Mathlib's own cache tool cannot remove the
# duplication.
#
# The whole workspace, not just Mathlib. A fresh worktree also builds batteries,
# aesop, Qq, importGraph, plausible, LeanSearchClient, proofwidgets, BrauerGroup,
# checkdecls and Cli, and Lake schedules Mathlib's module traces from those
# packages' oleans: with them missing, a worktree whose Mathlib tree was already
# shared still rebuilt 446-472 Mathlib modules, and four of those at once is what
# the disk could not carry. So every package in the manifest gets an entry, keyed
# by its own revision and the toolchain:
#
#   $STORE/<package>/<rev>-<toolchain>/lib/lean    one copy of the bytes
#   $STORE/<package>/<rev>-<toolchain>/ir          the cached IR, where there is one
#   .lake/packages/<package>/.lake/build/lib/lean  this worktree's links
#
# Most entries cost nothing to fill. Mathlib's cache tool already carries oleans
# for Batteries, Aesop, Qq, Cli, ImportGraph, LeanSearchClient, Plausible and
# ProofWidgets (Mathlib's `Cache/IO.lean:24-46`, `isPartOfMathlibCache`), and
# `lake exe cache get <Module>` decompresses one package's share of it in about a
# second. Only the packages that cache does not cover -- BrauerGroup and
# checkdecls here -- are compiled, once, and then shared like the rest.
#
# Traces are private to a worktree; everything else is shared. Lake deletes a
# module's `.olean` and its other outputs before rebuilding the module
# (`src/lean/lake/Lake/Build/Module.lean:744-753`, `Module.clearOutputArtifacts`),
# so a rebuild replaces an inode and leaves every other worktree's bytes alone.
# It does not do that for the `.trace` beside them: Lake rewrites a trace in
# place, and a trace records the absolute path of the source file it was built
# from (`Lake/Build/Module.lean:52-56`, the `inputFacet` trace). A rebuild in one
# worktree would therefore rewrite the trace other worktrees read to name a path
# that does not exist for them, and that module -- and everything importing it --
# would be rebuilt everywhere the entry is linked. The first version of this
# store was poisoned exactly that way. A linked tree therefore gets a copy of
# every `.trace` file and a hardlink for everything else: 8725 traces, about 9 MB
# per worktree, and no worktree can write into what another one reads.
#
# An entry is handed out only where Lake certifies it: `lake build --no-build
# +<Module>` must report the package's modules up to date against the sources at
# that revision and the packages they import, and an entry is seeded only from a
# tree that check passed on. Without that check the store could hand a second
# worktree the stale outputs #143 was about.
#
# One revision of a package is materialized once, under a per-key lock; every
# other worktree at that head links it in about a second. Nothing else is
# serialized -- each worktree still runs its own `lake update`, its own cache step
# and its own build, and no worktree's build waits for another's.
#
# Environment: MATHLIB_BUILD_STORE (default <git-common-dir>/lake-build-store),
# MATHLIB_BUILD_STORE_KEEP (entries to keep per package, default 2),
# MATHLIB_BUILD_STORE_MIN_FREE_GB (free space a decompression needs, default 7).
set -euo pipefail
cd "$(dirname "$0")/.."

PKGDIR=".lake/packages"
TOOL="$(tr -d '\n' < lean-toolchain | tr -cs 'A-Za-z0-9._-' '_')"

STORE="${MATHLIB_BUILD_STORE:-}"
if [ -z "$STORE" ]; then
  STORE="$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null \
    || echo .lake)/lake-build-store"
fi
KEEP="${MATHLIB_BUILD_STORE_KEEP:-2}"
MIN_FREE_GB="${MATHLIB_BUILD_STORE_MIN_FREE_GB:-7}"

say() { echo "cache-get: $*"; }
warn() { echo "cache-get: $*" >&2; }

[ -d "$PKGDIR/mathlib" ] || { warn "no Mathlib checkout at $PKGDIR/mathlib; run 'just update' first"; exit 1; }

# Every package of the manifest, Mathlib first: the others are built against it.
PACKAGES="$(python3 - <<'PY'
import json
names = [p["name"] for p in json.load(open("lake-manifest.json"))["packages"]]
print(" ".join(["mathlib"] + [n for n in names if n != "mathlib"]))
PY
)" || { warn "cannot read lake-manifest.json"; exit 1; }

pkg_dir() { printf '%s/%s' "$PKGDIR" "$1"; }
pkg_tree() { printf '%s/%s/.lake/build/lib/lean' "$PKGDIR" "$1"; }
pkg_ir() { printf '%s/%s/.lake/build/ir' "$PKGDIR" "$1"; }
pkg_rev() { git -C "$(pkg_dir "$1")" rev-parse HEAD 2>/dev/null; }
entry() { printf '%s/%s/%s-%s' "$STORE" "$1" "$2" "$TOOL"; }

# The module a package's library is rooted at: its namesake `.lean` file at the
# package root (Batteries.lean, Qq.lean, ...). `lake exe cache get` takes that
# module name, and so does the module-spec check that certifies the package.
pkg_root_module() {
  local d f b lc
  d="$(pkg_dir "$1")"
  lc="$(printf '%s' "$1" | tr '[:upper:]' '[:lower:]')"
  for f in "$d"/*.lean; do
    [ -e "$f" ] || continue
    b="$(basename "$f" .lean)"
    if [ "$(printf '%s' "$b" | tr '[:upper:]' '[:lower:]')" = "$lc" ]; then
      printf '%s' "$b"
      return 0
    fi
  done
  return 1
}

# A package checkout with local modifications is not described by its revision,
# so it can neither take a tree from the store nor seed one.
pkg_clean() {
  [ -z "$(git -C "$(pkg_dir "$1")" status --porcelain --untracked-files=no 2>/dev/null)" ]
}

# The olean count of a package's tree (0 when it has none).
pkg_oleans() {
  find "$(pkg_tree "$1")" -name '*.olean' -type f 2>/dev/null | wc -l
}

# Give $1's tree its own copy of every trace file: Lake rewrites traces in place
# and records absolute source paths in them (see the header), so a shared trace
# is a shared write target.
private_traces() {
  local f tmp
  while IFS= read -r -d '' f; do
    tmp="$f.private.$$"
    cp -p "$f" "$tmp" && mv -f "$tmp" "$f"
  done < <(find "$1" \( -name '*.trace' -o -name '*.trace.hash' \) -print0 2>/dev/null)
}

# Whether this worktree's tree already is $2's inodes.
linked() {
  local p="$1" e="$2" m a b
  m="$(pkg_root_module "$p")" || return 1
  a="$(stat -c '%d:%i' "$(pkg_tree "$p")/$m.olean" 2>/dev/null || echo none)"
  b="$(stat -c '%d:%i' "$e/lib/lean/$m.olean" 2>/dev/null || echo none)"
  [ "$a" = "$b" ] && [ "$a" != none ]
}

# Replace this worktree's tree with links into entry $2, keeping the traces private.
relink() {
  local p="$1" e="$2" t
  t="$(pkg_tree "$p")"
  say "$p: linking this worktree's tree to $e (nothing to fetch)"
  rm -rf "$t" "$(pkg_ir "$p")"
  mkdir -p "$(dirname "$t")"
  cp -al "$e/lib/lean" "$t"
  [ -d "$e/ir" ] && cp -al "$e/ir" "$(pkg_ir "$p")"
  private_traces "$t"
}

# Drop this worktree's tree, so it can be filled without touching any link.
unlink_tree() { rm -rf "$(pkg_tree "$1")" "$(pkg_ir "$1")"; }

# Lake's own check: $1's modules are up to date against their sources and the
# packages they import.
certify() {
  local p="$1" m out
  m="$(pkg_root_module "$p")" || return 0
  if out="$(lake build --no-build "+$m" 2>&1)"; then
    say "$p: $out"
    return 0
  fi
  warn "$p is not up to date:"
  printf '%s\n' "$out" | tail -n 3 >&2
  return 1
}

# Every package this worktree resolves, checked by Lake. Mathlib's check walks its
# whole import graph, so it covers the modules of the packages Mathlib imports as
# well; the other packages are checked on their own, which is what the root
# package's build needs from the ones Mathlib does not import.
certify_all() {
  local p bad=""
  for p in $PACKAGES; do
    [ -d "$(pkg_dir "$p")" ] || continue
    pkg_root_module "$p" >/dev/null || continue
    certify "$p" || bad="$bad $p"
  done
  [ -z "$bad" ]
}

free_gb() { df -BG --output=avail "$STORE" 2>/dev/null | tail -n 1 | tr -dc '0-9'; }

# Fill this worktree's own tree for one package: what Mathlib's cache carries for
# it, then a build only for what the cache does not cover.
fill() {
  local p="$1" m avail
  unlink_tree "$p"
  m="$(pkg_root_module "$p")" || { say "$p: no root module; leaving its tree empty"; return 0; }
  if [ "$p" = mathlib ]; then
    avail="$(free_gb)"
    if [ "${avail:-0}" -lt "$MIN_FREE_GB" ]; then
      warn "only ${avail:-0}G free; decompressing Mathlib needs about ${MIN_FREE_GB}G"
      warn "free space, or set MATHLIB_BUILD_STORE_MIN_FREE_GB"
      return 1
    fi
    say "$p: no entry for this revision; decompressing Mathlib's cache here"
    lake exe cache get
  else
    say "$p: taking what Mathlib's cache carries for it"
    lake exe cache get "$m" || true
  fi
  if [ "$(pkg_oleans "$p")" -eq 0 ]; then
    say "$p: Mathlib's cache does not cover it; building it once"
  fi
  lake build "+$m"
}

# Seed an entry from this worktree's certified tree: hardlinks beside the final
# name, then a rename, so no other worktree can read a half-written entry. The
# entry gets its own copies of the traces (see the header).
seed() {
  local p="$1" k="$2" e tmp
  e="$(entry "$p" "$k")"
  if [ "$(pkg_oleans "$p")" -eq 0 ]; then
    say "$p: nothing built, so nothing to seed"
    return 0
  fi
  tmp="$e.tmp.$$"
  rm -rf "$tmp"
  mkdir -p "$tmp/lib"
  cp -al "$(pkg_tree "$p")" "$tmp/lib/lean"
  [ -d "$(pkg_ir "$p")" ] && cp -al "$(pkg_ir "$p")" "$tmp/ir"
  private_traces "$tmp/lib/lean"
  rm -rf "$e"
  mv "$tmp" "$e"
  touch "$e/.complete"
  say "seeded $e ($(du -sh "$e" | cut -f1), $(pkg_oleans "$p") oleans)"
}

# Drop entries beyond the newest $KEEP of each package. Removing an entry only
# unlinks the store's links; worktrees already linked to it keep their bytes, so
# this can never break a running build.
prune() {
  local p d k kept
  for p in $PACKAGES; do
    kept=0
    for d in $(ls -1dt "$STORE/$p"/*/ 2>/dev/null); do
      k="$(basename "$d")"
      kept=$((kept + 1))
      [ "$kept" -le "$KEEP" ] && continue
      if flock -n "$STORE/$p/.$k.lock" rm -rf "$d" 2>/dev/null; then
        say "pruned $p/$k (keeping $KEEP)"
      fi
    done
  done
}

# This worktree's own tree, completed as before #148, for the cases where the
# store cannot be used: locally modified package checkouts, or nowhere to put the
# store. A tree that is linked into an entry is dropped first, so the cache tool
# never writes into bytes another worktree reads.
plain() {
  local p m rev e
  for p in $PACKAGES; do
    [ -d "$(pkg_dir "$p")" ] || continue
    m="$(pkg_root_module "$p")" || continue
    rev="$(pkg_rev "$p")" || continue
    e="$(entry "$p" "$rev")"
    if [ -f "$e/.complete" ] && linked "$p" "$e"; then unlink_tree "$p"; fi
    if [ "$p" = mathlib ]; then lake exe cache get; else lake exe cache get "$m" || true; fi
  done
  exit 0
}

mkdir -p "$STORE" 2>/dev/null || { warn "cannot create $STORE; completing this worktree's own tree only"; plain; }

COLD=""
for p in $PACKAGES; do
  [ -d "$(pkg_dir "$p")" ] || { say "$p: not in this workspace; skipping"; continue; }
  if ! pkg_clean "$p"; then
    warn "$(pkg_dir "$p") has local modifications; staying out of the shared store"
    plain
  fi
  rev="$(pkg_rev "$p")" || { say "$p: no revision (not a git checkout); skipping"; continue; }
  e="$(entry "$p" "$rev")"
  mkdir -p "$STORE/$p"
  exec 9>"$STORE/$p/.$rev-$TOOL.lock"
  if ! flock -n 9; then
    say "$p: another worktree is completing $rev; waiting for it"
    flock 9
  fi
  if [ -f "$e/.complete" ]; then
    if linked "$p" "$e"; then
      say "$p: this worktree's tree is already linked from $e, nothing to fetch"
    else
      relink "$p" "$e"
    fi
    touch "$e"
  else
    unlink_tree "$p"
    COLD="$COLD $p"
  fi
  exec 9>&-
done

# Fill what the store has no entry for, in the workspace order: Mathlib's cache
# first, so the packages built after it find its oleans in place.
for p in $COLD; do
  mkdir -p "$STORE/$p"
  exec 9>"$STORE/$p/.$(pkg_rev "$p")-$TOOL.lock"
  flock 9
  e="$(entry "$p" "$(pkg_rev "$p")")"
  if [ -f "$e/.complete" ]; then
    linked "$p" "$e" || relink "$p" "$e"
  else
    fill "$p"
  fi
  exec 9>&-
done

# One check over the whole workspace: the packages that were linked and the ones
# that were just filled are certified together, which is what the root package's
# build needs. An entry that fails it is dropped rather than handed to the next
# worktree, and every package is filled again from Mathlib's cache.
REFILLED=""
if ! certify_all; then
  warn "the workspace does not certify against the store; refilling every package"
  for p in $PACKAGES; do
    [ -d "$(pkg_dir "$p")" ] || continue
    pkg_clean "$p" || continue
    rm -rf "$(entry "$p" "$(pkg_rev "$p")")"
    fill "$p" || true
    REFILLED="$REFILLED $p"
  done
  certify_all || { warn "the workspace still does not certify; not touching the store"; exit 1; }
  for p in $REFILLED; do seed "$p" "$(pkg_rev "$p")"; done
fi

for p in $COLD; do
  rev="$(pkg_rev "$p")"
  e="$(entry "$p" "$rev")"
  [ -f "$e/.complete" ] || seed "$p" "$rev"
done

for p in $PACKAGES; do
  [ -d "$(pkg_dir "$p")" ] || continue
  m="$(pkg_root_module "$p")" || continue
  say "$p: $(pkg_oleans "$p") oleans at $(pkg_rev "$p" 2>/dev/null | cut -c1-12), toolchain $TOOL"
done

prune
