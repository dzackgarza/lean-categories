/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FanCoarsening
public import LeanCategories.AlgebraicGeometry.Toric.AffineToric

/-!
# Probes for #24, on the smallest inputs that decide them

The generalized-chamber probes use the empty set of irrelevant roots.  Then `W_J`
is trivial, so both sides of Proposition 4.17(1) must be the fundamental chamber.
These probes check the action and filtration conventions without requiring a
concrete root system.  The affine-toric probes are independent of the chamber
construction and retain their original zero-cone checks.
-/

@[expose] public section

open CategoryTheory _root_.AlgebraicGeometry LeanCategories.AlgebraicGeometry.Toric

namespace LeanCategories.Lattices.Valued

variable {ι M N : Type*} [DecidableEq ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) (b : P.Base) (B : P.InvariantForm)

omit [DecidableEq ι] in
/-- With no irrelevant roots, the standard parabolic subgroup is trivial. -/
lemma probe_irrelevantReflectionSubgroup_empty :
    irrelevantReflectionSubgroup P (∅ : Finset ι) = ⊥ := by
  simp [irrelevantReflectionSubgroup]

omit [DecidableEq ι] in
/-- With no irrelevant roots, the generalized chamber is the fundamental chamber. -/
lemma probe_generalizedChamber_empty :
    generalizedChamber P b B (∅ : Finset ι) = fundamentalChamber P b B := by
  classical
  rw [generalizedChamber, probe_irrelevantReflectionSubgroup_empty]
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨h, y, hy, rfl⟩
    have hh : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.property)
    subst h
    simpa using hy
  · intro hx
    exact ⟨1, x, hx, by simp⟩

/-- With no irrelevant roots, the active half-space intersection is also the
fundamental chamber. -/
theorem probe_activeHalfspaceIntersection_empty :
    activeHalfspaceIntersection P b B (∅ : Finset ι) = fundamentalChamber P b B := by
  rw [activeHalfspaceIntersection, probe_irrelevantReflectionSubgroup_empty]
  ext x
  constructor
  · intro hx i hi
    have h := hx i (by simp [hi]) 1
    simpa using h
  · intro hx i hi h
    have hh : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.property)
    subst h
    simpa using hx i (Finset.mem_filter.mp hi).1

end LeanCategories.Lattices.Valued

namespace LeanCategories.AlgebraicGeometry.Toric

open LeanCategories.Lattices.Valued

/-- The chart of the zero cone of `ℚ` is the spectrum of the semigroup algebra of the whole dual
space: `Spec ∘ semigroup algebra ∘ cone-dual` computed on the smallest cone. -/
theorem probe_affineToricScheme_bot :
    affineToricScheme (⊥ : PointedCone ℚ ℚ) =
      Spec (CommRingCat.of (semigroupAlgebra ↥(coneDual (⊥ : PointedCone ℚ ℚ)))) :=
  affineToricScheme_def _

/-- The identity law of the affine functor at the zero cone: the smallest possible inclusion. -/
theorem probe_affineToricFunctor_map_id :
    (affineToricFunctor.map (PLift.up (le_refl (⊥ : PointedCone ℚ ℚ))) :
        affineToricScheme (⊥ : PointedCone ℚ ℚ) ⟶ affineToricScheme (⊥ : PointedCone ℚ ℚ)) =
      𝟙 (affineToricScheme (⊥ : PointedCone ℚ ℚ)) :=
  affineToricSchemeMap_refl _

/-- The recorded variance: on the smallest inclusion, the cone inclusion of `⊥ ≤ ⊤` gives a
morphism `𝔸_⊥ ⟶ 𝔸_⊤`, and `Spec` of the dual map is its definition. -/
theorem probe_variance :
    (affineToricFunctor.map (PLift.up (bot_le : (⊥ : PointedCone ℚ ℚ) ≤ ⊤)) :
        affineToricScheme (⊥ : PointedCone ℚ ℚ) ⟶ affineToricScheme (⊤ : PointedCone ℚ ℚ)) =
      Spec.map (CommRingCat.ofHom
        (affineToricRingMap (bot_le : (⊥ : PointedCone ℚ ℚ) ≤ ⊤)).toRingHom) :=
  affineToricSchemeMap_is_dual_spec _

/-- The recorded convention is the covariant one. -/
theorem probe_toricRealizationVariance :
    toricRealizationVariance = ToricRealizationVariance.conesCovariant := (rfl)

end LeanCategories.AlgebraicGeometry.Toric
