---
title: "Duplication audit of formed-module arithmetic branch"
---

## Incident

The branch `feat/formed-module-arithmetic` added code without first applying the existing reuse audit. The audit already stated that most TODO-ALGEBRA work was assembly or comparison work.

## Confirmed duplication

- `fixedValueInclusion` repeats Mathlib `Grothendieck.ι`. The two functors have the same objects and maps.
- `scalarTowerTensorEquiv` is definitionally equal to Mathlib `TensorProduct.AlgebraTensorModule.cancelBaseChange ... .symm`.
- `IsIntegral` is tautological because `IntegralLatticeCat R` already means an `R`-valued lattice.
- `IsIntegralSubmodule` restates `P ≤ (rationalizedForm R L).dualSubmodule P` instead of using Mathlib `BilinForm.dualSubmodule`.

## Redundant K3 work

Before this branch, the repository already had `hyperbolicPlane`, `e8Lattice`, orthogonal sums, orthogonal powers, `k3Lattice`, and `k3FiniteLattice`. The K3 definition already was `U^3 ⊥ E8(-1)^2`.

The branch added rank theorems, `hyperbolicPlanePower`, and `negativeE8Power`. The K3 definition does not use the new names. The theorem `k3FiniteLattice_rank` directly simplifies the concrete carrier. It does not use the new generic rank theorems.

## Evidence boundary

This report compares base commit `7e18e77` with branch head `fbf2671`. It records confirmed duplicate or redundant work. It does not claim that every new declaration is duplicated.

## Prior warning

See `projects/github.com__dzackgarza__lean-categories/references/todo-algebra-mathlib-and-lean-source-reuse-audit`.

## Disposition on current `main`

The historical findings describe branch head `fbf2671`. They do not describe merged state `4777f6c`.

- `1d7ba63` replaced the custom fixed-fiber functor with an abbreviation of `Grothendieck.ι`.
- `5455718` removed `scalarTowerTensorEquiv` and uses `cancelBaseChange`.
- `1d28c67` removed the tautological `IsIntegral`.
- `7819e9d` made `IsIntegralSubmodule` use `BilinForm.dualSubmodule`. The project name remains. It does not define another metric dual.
- `89cbe83` removed the redundant orthogonal-power aliases and direct rank endpoints.
- `2024dd8` removed repeated genus witnesses.
- `1f7324f` made metric-dual containment a derived theorem.

The K3 lattice now uses `U³ ⊥ E₈²`, where bare `E₈` is negative definite. No `E₈(-1)` appears in its definition.

This disposition closes the recorded duplicates. It does not claim a complete reuse audit of every declaration on the former branch.
