# Validation guide

Prerequisites: the research image (constitution E5); `just cache`; no other Lean process
(`pgrep -a -x 'lean|lake'` prints nothing).

| Step | Command | Expected outcome |
| --- | --- | --- |
| Tier 1 of a task | `just loop <changed modules> <test module>` (feature 001 T001) | no error; the test module's `example` and `#guard_msgs` checks hold; under 300 s |
| Classifier laws | elaborate `CategoryTheory/OneCat/ReindexTests.lean` | the universal property and the identity, composition and pasting equivalences are theorems |
| Registry witnesses | elaborate `Catalogue/Registry/InterpretationTests.lean` | every snapshot row evaluates with its witness |
| Export | run the export recipe of T020 twice on one revision | identical JSON and DOT |
| Consumer | build `Integration/RegistryConsumer/` against a release tag | every needed row resolves by stable ID |
| Publication | `python3 scripts/publish_prove2me.py --dry-run --out .tmp/p2m` | every module outside the axiom guard and every card listed |
| Milestone | `just test` | all audits green |

The acceptance scenarios of [spec.md](spec.md) are the assertions of the test modules named in
[tasks.md](tasks.md).
