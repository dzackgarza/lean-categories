# Per-module elaboration times of every build (lean-categories#160)

Every `just build` and every `just test` leaves, in `build-timings/` at the root of this
repository, a record of the time each module took to elaborate. The question "which module
is slow" is answered from that record, not by a second build.

## Where the records are

```
build-timings/<commit>-<UTC start time>.log   the build's own report, unedited
build-timings/<commit>-<UTC start time>.tsv   its module lines: verb, caption, seconds
```

The name carries the commit built (`git rev-parse --short=12 HEAD`) and the run's start
time in UTC (`20261115T093500Z`), so runs of the same commit do not overwrite each other and
records they are kept in the order they were made. Example:
`build-timings/1e2793324635-20261115T093500Z.tsv`.

The directory is outside the build tree: `lake clean` does not remove it, and it is
`.gitignore`d because it is a record of a run, not a source file. `BUILD_TIMING_DIR` moves it.

CI runs the same entry point (`just test-ci` → `just test`), so every CI run of `main` writes the
same files, and the workflow uploads them as the `build-timings` artifact with this step
(`.github/workflows/ci.yml`, landed at `83ff077d53` with the orchestrator's `workflows` permission;
the agent connection has none, so a change to the step travels through a person):

```yaml
      - name: Upload the per-module elaboration times of this run
        if: always()
        uses: actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02 # v4.6.2
        with:
          name: build-timings
          path: build-timings/
          if-no-files-found: error
          retention-days: 90
```

`if-no-files-found: error`, not `warn`: `scripts/build-timing.sh` writes a record on every build, so
an upload with nothing in it is a broken build step and should fail the job, not pass quietly.

## Which modules a record covers

A record holds the modules *that build elaborated*; a module Lake replayed from its trace is not
in it. Two builds are recorded, because they cover different sets:

* `just build` runs `lake build`, the repository's default target: the closure of the root module
  `LeanCategories.lean`, which is 191 of this library's 1187 modules.
* the `vacuity-audit` step of `just test` builds `LeanCategories.Tools.VacuityAudit`, which
  imports `LeanCategories.All` and so elaborates the whole library. Its record is the one to
  read for "which module is slow", and a `just test` writes both — one file per build step, each
  named by the commit and by that step's start time.

## What is recorded, and by whom

By Lake, not by us. Lake times each build job it runs (`Lake/Build/Common.lean:331`, the
elapsed time of the job's action) and prints that time beside the job's caption when it prints
the caption at all (`Lake/Build/Run.lean:230`, `showTime := isVerbose || !useAnsi`; `Run.lean:138`
prints `<verb> <caption> (<time>)`). `scripts/build-timing.sh` runs `lake build --no-ansi`, keeps
that report verbatim as the `.log`, and extracts its module lines into the `.tsv`; it takes no
timing of its own. `--no-ansi` matters: a job's caption is printed only when Lake is not in ANSI
mode (`Run.lean:130`, `showJob := ... || showProgress && !useAnsi && ...`), and its mode is
`--ansi=auto`, which reads `TERM` — unset under `just`, so the captions were withheld there and a
record came out empty.

A module's own job is the elaboration that writes its `.olean` and `.ilean`
(`Built LeanCategories.ForMathlib.Cofibered (3.4s)`); the `:irArts` job that follows is the
code generation. Both appear in the `.tsv`, the elaboration first, so the row for a module's
elaboration is
`Built <Module> <seconds>`. Jobs of dependency packages (Mathlib among them) appear with their
own module names, which is why the first full build of a fresh worktree lists them.

## Reading a record

Largest elaborations of a run first:

```bash
sort -t $'\t' -k3,3gr build-timings/<file>.tsv | head -20
```

All runs of this library's own modules, worst first:

```bash
grep -h '^Built\tLeanCategories' build-timings/*.tsv | sort -t $'\t' -k3,3gr | head -20
```

## What a record does not contain

* **A module Lake replayed.** A build that changes one module rebuilds that module and
  everything above it; the rest are replayed from their traces, take no time, and Lake prints
  no time for them (`Replayed <Module>`, with `buildTime = 0`). A run's `.tsv` is therefore
  the record of what that run elaborated. The record of a commit's whole library is its first
  full build, which is what a fresh worktree and CI both do.
* **A bare `lake build`.** Lake has no post-build hook and this repository cannot intercept
  its own `lake` binary, so builds are recorded only through the repository's entry points,
  `just build` and `just test`; both run `scripts/build-timing.sh`. Nothing else in the
  repository or in CI invokes `lake build` for the acceptance build.
* **The other gate steps of `just test`.** The mathlib-lint, unused-variable and axiom-audit
  steps build little of their own beyond what the two recorded builds elaborated.
