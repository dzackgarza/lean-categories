# Validation guide

Prerequisites: the research image (constitution E5); `just cache`; no other Lean process
(`pgrep -a -x 'lean|lake'`).

| Step | Command | Expected outcome |
| --- | --- | --- |
| Tier 1 of a task | `just loop <modules>` (T001, the first task) for each changed module and its test modules | no error; the test module's `#guard_msgs` and `example` checks hold; under 300 s |
| Registry state | elaborate `Catalogue/Registry/SnapshotTests.lean` | the new rows are in the snapshot |
| Milestone | `just test` | all audits green for the files of this feature |
| Consumer check | the kernel task that consumes the issue reads the row at the pinned revision | outside this repository; named in each task |

The acceptance scenarios of [spec.md](spec.md) are the assertions of the test modules named in
[plan.md](plan.md).
