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
# An entry lives exactly while some worktree names it. A store that keeps one
# 6.7 GB Mathlib entry per revision it has ever seen grows as often as Mathlib
# master moves, not as often as anyone builds: on 2026-11-13 it held the head this
# worktree was on, the head it had left, and a revision a third worktree had
# resolved, and the VM's one disk stood at 9 GB free with three Lean chats stopped
# (lean-categories#149). So after linking, this script drops every entry -- of
# every package, not only the ones this workspace resolves -- whose revision no
# worktree of this repository names in its `lake-manifest.json`, and every
# unfinished seed whose process is gone; it never drops an entry a running build
# reads, nor one another worktree is filling or linking. See `gc` and `in_use`.
#
# One revision of a package is materialized once, under a per-key lock; every
# other worktree at that head links it in about a second. Nothing else is
# serialized -- each worktree still runs its own `lake update`, its own cache step
# and its own build, and no worktree's build waits for another's.
#
# Environment: MATHLIB_BUILD_STORE (default <git-common-dir>/lake-build-store),
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
MIN_FREE_GB="${MATHLIB_BUILD_STORE_MIN_FREE_GB:-7}"

say() { echo "cache-get: $*"; }
warn() { echo "cache-get: $*" >&2; }

[ -d "$PKGDIR/mathlib" ] \
  || { warn "no Mathlib checkout at $PKGDIR/mathlib; run 'just update' first"; exit 1; }

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
# module name, and so does the module-spec check that certifies the package. $2
# is the `packages` directory holding the checkout, this worktree's by default.
pkg_root_module() {
  local d f b lc
  d="$(pkg_dir "$1" "${2:-$PKGDIR}")"
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

# Whether the tree $1 has in worktree $3 (this worktree by default) already is
# $2's inodes.
linked() {
  local p="$1" e="$2" base="${3:-$PKGDIR}" m a b
  m="$(pkg_root_module "$p" "$base")" || return 1
  a="$(stat -c '%d:%i' "$base/$p/.lake/build/lib/lean/$m.olean" 2>/dev/null || echo none)"
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

# ---- Eviction: an entry lives while a worktree's manifest names it -----------
#
# The store used to keep the newest two entries of each package, which is not a
# property of anything: it held the head this worktree was on, the head it had
# left, and whatever a third worktree had resolved, so one 6.7 GB Mathlib entry
# accumulated per master head either way and the VM's disk filled
# (lean-categories#149). The rule below is the one the entries already describe --
# an entry is <package>/<rev>-<toolchain> -- read from every worktree of this
# repository instead of from the two newest.

# Every worktree of this repository, one absolute path per line. One whose
# directory has been deleted is still listed; it has no manifest, so it names
# nothing.
worktrees() { git worktree list --porcelain | sed -n 's/^worktree //p'; }

# "<package> <revision>" for every package of every worktree's manifest.
named_revs() {
  local w
  while IFS= read -r w; do
    [ -f "$w/lake-manifest.json" ] || continue
    python3 - "$w/lake-manifest.json" <<'PY' || true
import json, sys
try:
    manifest = json.load(open(sys.argv[1]))
except Exception:
    sys.exit(0)
for package in manifest.get("packages", []):
    if package.get("rev"):
        print(package["name"], package["rev"])
PY
  done < <(worktrees)
}

# The revision an entry directory is keyed by: its name is <rev>-<toolchain>, and
# Lake writes a revision as the 40 hex digits of the commit. `seed` can also leave
# <rev>-<toolchain>.tmp.<pid> behind when it is interrupted, which is no entry.
entry_rev() {
  local k="${1%%.tmp.*}"
  if [[ "$k" =~ ^([0-9a-f]{40}) ]]; then printf '%s' "${BASH_REMATCH[1]}"
  else printf '%s' "$k"; fi
}

# What a running build reads: "<package>/<key>" for store entries, "<worktree>"
# for worktrees that have a Lean process working in them.
#
# A linked tree is hardlinks, so a build in a worktree opens that worktree's own
# paths and never $STORE: the bytes it reads are the entry's inodes under another
# name. Two things therefore put an entry in use.
#   * A process holds a path inside the entry itself -- another worktree's
#     `cp -al`, a `du`, a seed being written. Read off /proc/<pid>/fd and
#     /proc/<pid>/maps, since Lean maps an `.olean` and closes the descriptor it
#     opened it with, so descriptors alone would miss a build.
#   * A `lake`, `lean` or `leanc` process is working inside a worktree whose tree
#     is that entry's inodes: a build that started before this run and has not
#     finished. It must survive even though no manifest names it any more, because
#     its worktree has moved on to another head.
#   * Some process has a path open under a worktree's `.lake`, which is a
#     `lake update`, a build or a `lake exe` in that worktree. Its manifest may be
#     mid-write and name nothing at this instant, so the worktree's tree is treated
#     as in use and its entries are kept rather than trusted to the manifest.
# This script's own process tree is excluded: it is the process that just decided
# about the entry, and it holds every entry it linked from.
in_use() {
  local wts=() line p d w
  while IFS= read -r w; do wts+=("$w"); done < <(worktrees)
  while IFS= read -r line; do
    case "${line%% *}" in
      E) printf '%s\n' "${line#* }" ;;
      W) w="${line#* }"
         for p in $(ls -1 "$w/.lake/packages" 2>/dev/null); do
           [ -d "$STORE/$p" ] || continue
           for d in "$STORE/$p"/*/; do
             [ -d "$d" ] || continue
             if linked "$p" "$d" "$w/.lake/packages"; then
               printf '%s\n' "$p/$(basename "$d")"
             fi
           done
         done ;;
    esac
  done < <(python3 - "$STORE" "$$" "${wts[@]}" <<'PY'
import os, sys

store = os.path.realpath(sys.argv[1])
mine = int(sys.argv[2])
worktrees = [os.path.realpath(w) for w in sys.argv[3:]]
lean = ("lake", "lean", "leanc")


def ppid_of(pid):
    try:
        with open("/proc/%d/stat" % pid) as f:
            return int(f.read().rsplit(") ", 1)[1].split()[1])
    except (OSError, IndexError, ValueError):
        return 0


pids = [int(p) for p in os.listdir("/proc") if p.isdigit()]
parent = {p: ppid_of(p) for p in pids}


def ours(pid):
    for _ in range(64):
        if pid == mine:
            return True
        pid = parent.get(pid, 0)
        if not pid:
            return False
    return False


def below(path, root):
    return path == root or path.startswith(root + os.sep)


def read(path):
    try:
        return os.readlink(path)
    except OSError:
        return ""


seen = set()
for pid in pids:
    if ours(pid):
        continue
    cwd = read("/proc/%d/cwd" % pid)
    if cwd and os.path.basename(read("/proc/%d/exe" % pid)) in lean:
        for w in worktrees:
            if below(cwd, w) and ("W " + w) not in seen:
                seen.add("W " + w)
                print("W " + w)
    held = []
    for fd in os.listdir("/proc/%d/fd" % pid) if os.access("/proc/%d/fd" % pid, os.R_OK) else []:
        held.append(read("/proc/%d/fd/%s" % (pid, fd)))
    try:
        with open("/proc/%d/maps" % pid) as f:
            for line in f:
                fields = line.split(None, 5)
                if len(fields) == 6:
                    held.append(fields[5].rstrip("\n"))
    except OSError:
        pass
    for path in held:
        path = path.split(" (deleted)")[0]
        if not path.startswith("/"):
            continue
        for w in worktrees:
            if below(path, os.path.join(w, ".lake")) and ("W " + w) not in seen:
                seen.add("W " + w)
                print("W " + w)
        if not below(path, store):
            continue
        parts = path[len(store) + 1:].split(os.sep)
        if len(parts) >= 3 and ("E " + parts[0] + "/" + parts[1]) not in seen:
            seen.add("E " + parts[0] + "/" + parts[1])
            print("E " + parts[0] + "/" + parts[1])
PY
)
}

# Drop every entry no worktree names, and every unfinished seed whose process is
# gone. A removal holds the entry's own per-key lock, so it cannot land inside
# another worktree's `fill` or `relink` of that key, and an entry a running build
# reads is skipped (`in_use`) along with an unfinished seed a live process owns.
#
# Removing an entry only unlinks the store's names for its inodes. A hardlinked
# file gives up its disk space when its last link goes, so the space comes back
# when the last worktree linked to it relinks (`unlink_tree` in `fill`) or is
# deleted -- never before. A worktree that is registered but never relinks, such
# as one left behind by a stopped chat, keeps its 6.7 GB to itself and this script
# cannot reclaim it; `du -sh .lake/packages` in that worktree shows it, and its
# `lake-manifest.json` also keeps alive the entry it names.
human() { numfmt --to=iec --suffix=B "${1:-0}" 2>/dev/null || printf '%sB' "${1:-0}"; }

gc() {
  local named inuse p d k rev size note pid dropped=0 freed=0
  named="$(named_revs | sort -u)"
  inuse="$(in_use | sort -u)"
  for p in $(ls -1 "$STORE" 2>/dev/null); do
    [ -d "$STORE/$p" ] || continue
    for d in "$STORE/$p"/*/; do
      [ -d "$d" ] || continue
      k="$(basename "$d")"
      rev="$(entry_rev "$k")"
      note=""
      case "$k" in
        *.tmp.*)
          pid="${k##*.tmp.}"
          if grep -qa 'cache-get\.sh' "/proc/$pid/cmdline" 2>/dev/null; then
            continue
          fi
          note=" (an interrupted seed)" ;;
        *)
          if printf '%s\n' "$named" | grep -qxF -- "$p $rev"; then continue; fi
          if printf '%s\n' "$inuse" | grep -qxF -- "$p/$k"; then
            say "$p/$k: kept; a running build reads it"
            continue
          fi ;;
      esac
      size="$(du -sb "$d" 2>/dev/null | cut -f1)"
      if flock -n "$STORE/$p/.$k.lock" rm -rf "$d" 2>/dev/null; then
        dropped=$((dropped + 1))
        freed=$((freed + ${size:-0}))
        say "dropped $p/$k$note ($(human "${size:-0}")): no worktree names it"
      else
        say "$p/$k: kept; another worktree is filling or linking it"
      fi
    done
  done
  if [ "$dropped" -gt 0 ]; then
    say "store: dropped $dropped entries, $(human "$freed") of entry bytes"
  else
    say "store: every entry is named by some worktree's manifest"
  fi
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

mkdir -p "$STORE" 2>/dev/null \
  || { warn "cannot create $STORE; completing this worktree's own tree only"; plain; }

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

# Evict now that every package with an entry is linked, and before anything is
# decompressed: the head this worktree has left is named by no manifest any more,
# so its 6.7 GB come back here -- through the `unlink_tree` the fill below does --
# instead of after the next 6.7 GB has been written beside them.
gc

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

# And once more at the end: the entries this run seeded are named now, and one a
# concurrent worktree left unnamed while this run was filling is dropped here.
gc
