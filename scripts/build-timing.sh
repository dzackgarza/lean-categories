#!/usr/bin/env bash
# Keep the per-module elaboration times of a build (lean-categories#160).
#
# Lake times every job it runs and prints that time beside the job's caption
# (`Lake/Build/Run.lean:230`: `showTime := isVerbose || !useAnsi`, and `:138` prints
# `<verb> <caption> (<time>)`), e.g.
#
#   ✔ [1208/1209] Built LeanCategories.ForMathlib.Cofibered (3.4s)
#
# A module's own job is the elaboration that writes its `.olean`/`.ilean` (`Built <Module>`);
# its `:irArts` job is the code generation that follows it. This script keeps that report
# verbatim -- it times nothing itself -- and extracts the module lines from it:
#
#   build-timings/<commit>-<UTC start time>.log   the build's own report, unedited
#   build-timings/<commit>-<UTC start time>.tsv   its module lines, one row per job:
#                                                 verb, caption, seconds
#
# One file per run, named by the commit built and the run's start time, so two runs of the
# same commit do not overwrite each other. The directory is outside the build tree
# (`.lake/`), so `lake clean` does not remove it; it is `.gitignore`d (a record, not a
# source), and CI uploads it as an artifact with 90-day retention
# (`.github/workflows/ci.yml`). `docs/build-timings.md` states the location and the format.
#
# Lake prints a job's caption only when it is not using ANSI output (`Lake/Build/Run.lean:130`,
# `showJob := ... || showProgress && !useAnsi && ...`), and its time only beside that caption.
# Piping through `tee` is not enough to settle that: Lake's decision is `cfg.ansiMode.isEnabled`,
# which with `--ansi=auto` reads `TERM`, and under `just` `TERM` is unset. So the build is run
# with `--no-ansi`, which fixes the mode rather than relying on the terminal.
#
# Usage: scripts/build-timing.sh [<lake build arguments>...]
set -euo pipefail
cd "$(dirname "$0")/.."

DIR="${BUILD_TIMING_DIR:-build-timings}"
COMMIT="$(git rev-parse --short=12 HEAD 2>/dev/null || echo unknown)"
START="$(date -u +%Y%m%dT%H%M%SZ)"
LOG="$DIR/$COMMIT-$START.log"
TSV="$DIR/$COMMIT-$START.tsv"
mkdir -p "$DIR"

echo "build-timing: commit $COMMIT, started $START UTC; report -> $LOG"
set +e
lake build --no-ansi "$@" 2>&1 | tee "$LOG"
STATUS="${PIPESTATUS[0]}"
set -e

# The module lines of that report. A job's time is what Lake printed: `(<n>ms)` or
# `(<n>.<d>s)`, at the end of an `[<i>/<n>]` line.
{
  printf 'verb\tcaption\tseconds\n'
  sed -nE 's/^.*\[[0-9]+\/[0-9]+\] (Built|Ran) ([^ ]+) \(([0-9]+(\.[0-9]+)?)(ms|s)\)[[:space:]]*$/\1\t\2\t\3\t\5/p' "$LOG" |
    awk -F'\t' -v OFS='\t' '$4 == "ms" { printf "%s\t%s\t%.3f\n", $1, $2, $3 / 1000; next }
      { printf "%s\t%s\t%.3f\n", $1, $2, $3 }'
} >"$TSV"

JOBS="$(($(wc -l <"$TSV") - 1))"
echo "build-timing: $JOBS timed module jobs -> $TSV"
exit "$STATUS"
