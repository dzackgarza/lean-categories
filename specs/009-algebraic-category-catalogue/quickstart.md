# Quickstart: validate the algebraic categories

Run from the repository root on the research image; `pgrep -a -x 'lean|lake'` prints nothing first.

| Step | Command | Expected outcome |
| --- | --- | --- |
| Tier 1 of a task | `just loop <changed modules> <test module>` (feature 001 T001) | no error; under 300 s |
| Tower | elaborate `Catalogue/Semantics/Algebra/DivisibilityTowerTests.lean` | $\mathbb Z$ reaches UFDs through the functors; $\mathbb Z[x]$ is not a PID |
| Groups | elaborate `Catalogue/Semantics/Algebra/GroupTests.lean` | invariant factors $(2, 12)$ for $\mathbb Z/4 \times \mathbb Z/6$ |
| Complexes | elaborate `Catalogue/Semantics/Modules/ComplexesTests.lean` | the long exact sequence elaborates; $d^2 \neq 0$ is refused |
| Registry | elaborate `Catalogue/Registry/SnapshotTests.lean` | every row of the feature is listed |
| Milestone | `just test` | all audits green |
