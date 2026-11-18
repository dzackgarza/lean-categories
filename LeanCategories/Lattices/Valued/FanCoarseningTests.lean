/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FanCoarsening
public import LeanCategories.AlgebraicGeometry.Toric.AffineToric

/-!
# Probes for #24, on the smallest inputs that decide them

Each declaration here is a concrete instance that decides one obligation of #24 on an input small
enough to read off the answer.

* The coarsening item: the fan whose only cone is the zero cone, over the lattice `ℤ ⊆ ℚ`, coarsened
  by the trivial folding. This decides that `IsFanCoarsening` is *satisfiable* (so
  `coarsenFan`/`coarsenFunctor` are not vacuous), that `coarsenedCones` of the trivial folding is
  the identity, and that equivariance and local finiteness hold there.
* The toric item: the affine toric functor at the zero cone of `ℚ`, where the identity law and the
  recorded variance are checked on the smallest possible inclusion.
-/

@[expose] public section

open CategoryTheory _root_.AlgebraicGeometry LeanCategories.AlgebraicGeometry.Toric
  LeanCategories.Lattices.Valued.FoldingData

namespace LeanCategories.Lattices.Valued

/-- The lattice `ℤ` inside `ℚ`. -/
def probeLattice : ℤ →+ ℚ := Int.castAddHom ℚ

/-- The fan of `ℚ` whose only cone is the zero cone. -/
def probeZeroFan : Fan probeLattice where
  cones := {⊥}
  finite_cones := Set.finite_singleton _
  isToricCone := by
    rintro σ (rfl : σ = (⊥ : PointedCone ℚ ℚ))
    exact ⟨⟨∅, by simp⟩, fun x (hx : x ∈ (⊥ : PointedCone ℚ ℚ)) hx0 _ => hx0 (by simpa using hx)⟩
  mem_of_isFaceOf := by
    rintro σ τ (rfl : σ = (⊥ : PointedCone ℚ ℚ)) hτ
    have hτbot : τ = (⊥ : PointedCone ℚ ℚ) := le_bot_iff.mp hτ.le
    rw [hτbot]
    exact Set.mem_singleton ⊥
  inf_isFaceOf_left := by
    rintro σ τ (rfl : σ = (⊥ : PointedCone ℚ ℚ)) (rfl : τ = (⊥ : PointedCone ℚ ℚ))
    rw [inf_idem]

/-- The trivial folding of `ℤ ⊆ ℚ`. -/
def probeFolding : FoldingData probeLattice := FoldingData.trivialFolding probeLattice

/-- The coarsening by the probe folding is the identity on cones. -/
theorem probeFolding_orbitJoin (C : PointedCone ℚ ℚ) : probeFolding.orbitJoin C = C :=
  FoldingData.orbitJoin_trivial C

/-- The coarsening by the trivial folding is the identity on the cone set of the zero fan: the
coarsened family is the original family. -/
theorem probe_coarsenedCones :
    probeFolding.coarsenedCones probeZeroFan = probeZeroFan.cones := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro D ⟨C, hC, rfl⟩
    rw [probeFolding_orbitJoin]
    exact hC
  · intro C hC
    exact ⟨C, hC, probeFolding_orbitJoin C⟩

/-- Equivariance, at the trivial folding and the zero fan: the coarsened family is stable under the
folding group. -/
theorem probe_coarsenedCones_stable :
    (fun D : PointedCone ℚ ℚ => D.map (((1 : probeFolding.group) : ℚ ≃ₗ[ℚ] ℚ) : ℚ →ₗ[ℚ] ℚ)) ''
        probeFolding.coarsenedCones probeZeroFan =
      probeFolding.coarsenedCones probeZeroFan :=
  probeFolding.coarsenedCones_stable probeZeroFan 1

/-- Local finiteness, at the trivial folding and the zero fan. -/
theorem probe_locallyFinite :
    ConeFamilyLocallyFinite (probeFolding.coarsenedCones probeZeroFan) :=
  probeFolding.coarsenedCones_locallyFinite probeZeroFan

/-- The coarsening predicate is satisfiable: the zero fan is `IsFanCoarsening` for the trivial
folding, so the coarsened fan and the coarsening functor are not vacuous. -/
theorem probe_isFanCoarsening : probeFolding.IsFanCoarsening probeZeroFan := by
  refine ⟨?_, ?_, ?_⟩
  · rintro C hC
    rw [probeFolding_orbitJoin]
    exact (probeZeroFan.isToricCone hC).salient
  · rintro C hC τ hτ
    have hCbot : C = (⊥ : PointedCone ℚ ℚ) := by simpa [probeZeroFan] using hC
    rw [hCbot, probeFolding_orbitJoin] at hτ
    have hτbot : τ = (⊥ : PointedCone ℚ ℚ) := le_bot_iff.mp hτ.le
    refine ⟨τ, ?_, ?_⟩
    · rw [hτbot]
      exact Set.mem_singleton ⊥
    · rw [probeFolding_orbitJoin, hτbot]
  · rintro C hC C' hC' τ hτ υ hυ
    have hCbot : C = (⊥ : PointedCone ℚ ℚ) := by simpa [probeZeroFan] using hC
    rw [hCbot, probeFolding_orbitJoin] at hτ
    have hτbot : τ = (⊥ : PointedCone ℚ ℚ) := le_bot_iff.mp hτ.le
    rw [hτbot, bot_inf_eq]

/-- The coarsened fan of the zero fan, by the trivial folding. -/
noncomputable def probeCoarsenedFan : Fan probeLattice :=
  probeFolding.coarsenFan probeZeroFan probe_isFanCoarsening

/-- The coarsened fan has the cone set of the original fan. -/
theorem probeCoarsenedFan_cones : probeCoarsenedFan.cones = probeZeroFan.cones :=
  probe_coarsenedCones

/-- The coarsening functor, on the coarsenable zero fan. -/
noncomputable def probeCoarsenFunctor : CoarsenableFan probeFolding ⥤ Fan probeLattice :=
  probeFolding.coarsenFunctor

/-- The coarsening functor sends the zero fan to the coarsened fan. -/
theorem probeCoarsenFunctor_obj :
    probeCoarsenFunctor.obj ⟨probeZeroFan, probe_isFanCoarsening⟩ = probeCoarsenedFan := (rfl)

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
