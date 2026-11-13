/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.PointedConeMinkowskiWeyl

/-!
# The duality of finitely generated rational cones (#139)

For a finitely generated pointed cone σ over ℚ — the cones of
`RationalPolyhedralCone.lean`, whose carrier is the rational span ℚ ⊗ ℤ over the
integers of a lattice — this file proves the two halves of the Cox–Little–Schenck
Proposition 1.2.4 (p. 24): the dual cone is finitely generated, and the biduality
holds.

The dual cone is taken with the evaluation pairing `Module.Dual.eval ℚ V` in the
dual space `Module.Dual ℚ V`, and the bidual with the identity pairing on the dual
space, exactly as `RationalPolyhedralCone.lean` documents them. Finite generation of
the dual cone needs the ambient space finite-dimensional over ℚ — which the rational
span of a lattice is — while the biduality holds in arbitrary dimension.

## Provenance

The two declarations are glue over the TauCeti/Mei port of the Minkowski–Weyl theorem
(`LeanCategories.ForMathlib.PointedConeMinkowskiWeyl`: `fg_iff_dualFG`,
`Submodule.FG.cone_dual_dual_flip_id`), itself ported from
`TauCeti/Geometry/Convex/Cone/MinkowskiWeyl.lean` and `FiniteDuality.lean`, adapted
from `Mei/Geometry/Convex/Cone/MinkowskiWeyl.lean` and `FiniteDuality.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei) at commit
`68536122a97fed8e87bc6870b9427151971b9ab2`, licensed under Apache 2.0. The finite
generation of σ^∘ is Mathlib’s `PointedCone.DualFG.dual_of_fg` composed with the port’s
`DualFG.fg`; the biduality is the port’s `Submodule.FG.cone_dual_dual_flip_id` — the
transport from the port’s `id.flip` pairing to the evaluation pairing is definitional
(`Module.Dual.eval` is by definition `LinearMap.flip LinearMap.id`).

## LC-09 search record (2026-11-13)

Formalization-corpus queries under several formulations, each recorded with hits:
`fg_iff_dualFG` (TauCeti MinkowskiWeyl.lean: the exact theorem; TauCetiRoadmap
Suggested.lean: a consumer), `cone_dualFG` (TauCeti MinkowskiWeyl.lean),
`dual_dual_flip` (TauCeti MinkowskiWeyl.lean, FiniteDuality.lean; Mathlib
Geometry/Convex/Cone/Dual.lean: `dual_dual_flip_dual`, `dual_flip_dual_dual_flip`),
`cone_dual_dual_flip` (TauCeti MinkowskiWeyl.lean, FiniteDuality.lean, and
Geometry/Toric/Algebraic/Cone/RationalDuality.lean: the reference implementation
that ports here), `Minkowski Weyl` (atlas-lean MinkowskiWeyl.lean twice; TauCeti
MinkowskiWeyl.lean), `dual cone finitely generated` (Mathlib DualFinite.lean),
`bipolar cone` (TauCeti FiniteDuality.lean), `subset_dual_dual` (TauCeti
FiniteDuality.lean; Mathlib Geometry/Convex/Cone/Dual.lean: `subset_dual_dual`
itself), `content:fg_iff_dualFG` (the exact-named theorem, both hits), `rational cone
duality` (TauCeti RationalDuality.lean), `Cox Little Schenck toric` (TauCeti
fan/Ray.lean), `PointedCone.hull dual` (atlas-lean LinearProgrammingDuality.lean).
The negative searches recorded with hits. The hit that decides the port route: TauCeti’s
`RationalDuality.lean` (itself from Mei at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`) is the reference implementation whose
carrier this file re-uses; every formal declaration in the file is that port’s, imported
with its provenance, and the glue here is the minimal ∘-definition — evaluation-pairing
restatements of the port’s own `Submodule.FG.cone_dual_dual_flip_id` and the `DualFG.dual_of_fg`
composition.

## References

* David Cox, John Little, Hal Schenck, *Toric Varieties*, Graduate Studies in
  Mathematics 124, American Mathematical Society (2011), Definition 1.2.3 and
  Proposition 1.2.4, p. 24. Zotero item `UYAMB8YC`.
-/

@[expose] public section

/-- The dual cone σ^∘ of a finitely generated pointed cone over ℚ is
finitely generated (Cox–Little–Schenck, GSM 124, Proposition 1.2.4, p. 24). The ambient
space is finite-dimensional over ℚ, as the rational span ℚ ⊗ ℤ over the integers of a
lattice is. -/
theorem _root_.Submodule.FG.dual_cone_fg {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {σ : PointedCone ℚ V} (hσ : σ.FG) :
    (PointedCone.dual (Module.Dual.eval ℚ V) σ).FG :=
  (PointedCone.DualFG.dual_of_fg (Module.Dual.eval ℚ V) hσ).fg

/-- The biduality (σ^∘)^∘ = σ (Cox–Little–Schenck, GSM 124, Proposition 1.2.4, p. 24): the
double dual of a finitely generated pointed cone over ℚ is the cone itself. No
finite-dimensionality or topological hypothesis is needed. -/
theorem _root_.Submodule.FG.dual_cone_dual_dual {V : Type*} [AddCommGroup V] [Module ℚ V]
    {σ : PointedCone ℚ V} (hσ : σ.FG) :
    PointedCone.dual (LinearMap.id : Module.Dual ℚ V →ₗ[ℚ] Module.Dual ℚ V)
      (PointedCone.dual (Module.Dual.eval ℚ V) σ) = σ :=
  hσ.cone_dual_dual_flip_id
