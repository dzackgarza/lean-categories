/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.JordanSplitting
public import LeanCategories.Lattices.Valued.RankOneDual

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

section SpanSingleton

variable (L : IntegralLatticeCat R) (v : L.obj.carrier) (hne : L.obj.pairing v v ≠ 0)

include hne in
/-- Scaling `v` is injective when its self-pairing is nonzero. -/
theorem injective_toSpanSingleton :
    Function.Injective (LinearMap.toSpanSingleton R L.obj.carrier v) := by
  intro a b hab
  have h : L.obj.pairing v (a • v) = L.obj.pairing v (b • v) := by
    simpa [LinearMap.toSpanSingleton_apply] using congrArg (L.obj.pairing v) hab
  rw [BilinModuleCat.pairing_smul_right, BilinModuleCat.pairing_smul_right, smul_eq_mul,
    smul_eq_mul] at h
  exact mul_right_cancel₀ hne h

/-- The line spanned by a vector of nonzero self-pairing is free of rank one on it. -/
noncomputable def spanSingletonBasis : Module.Basis (Fin 1) R ↥(R ∙ v) :=
  (Module.Basis.singleton (Fin 1) R).map
    ((LinearEquiv.ofInjective _ (injective_toSpanSingleton L v hne)).trans
      (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range R L.obj.carrier v).symm))

@[simp]
theorem spanSingletonBasis_apply :
    (spanSingletonBasis L v hne 0 : L.obj.carrier) = v := by
  simp [spanSingletonBasis]

end SpanSingleton

section Component

variable (L : IntegralLatticeCat R) (v : L.obj.carrier) (hne : L.obj.pairing v v ≠ 0)
  [Module.Projective R ↥(R ∙ v)]

/-- The rank-one basis of the sublattice carried by the line of `v`.

The carrier of the restricted form is the submodule itself, so this is the same basis read
with the module instances of the sublattice. -/
noncomputable def formedSublatticeSpanSingletonBasis :
    Module.Basis (Fin 1) R (formedSublattice L (R ∙ v)).obj.carrier :=
  spanSingletonBasis L v hne

/-- The rank-one sublattice on the line of `v` inherits the self-pairing of `v`. -/
theorem pairing_formedSublattice_spanSingletonBasis :
    (formedSublattice L (R ∙ v)).obj.pairing (formedSublatticeSpanSingletonBasis L v hne 0)
        (formedSublatticeSpanSingletonBasis L v hne 0) = L.obj.pairing v v := by
  change L.obj.pairing (spanSingletonBasis L v hne 0 : L.obj.carrier)
    (spanSingletonBasis L v hne 0 : L.obj.carrier) = L.obj.pairing v v
  rw [spanSingletonBasis_apply]

include hne in
/-- A line whose self-pairing is `u * π ^ e` is a `π ^ e`-modular sublattice.

This is a Jordan component of `L`: a rank-one modular lattice sitting inside `L`. -/
theorem isIModular_formedSublattice_span_singleton (π : R) (u : Rˣ) (e : ℕ) (hπ : π ≠ 0)
    (hvv : L.obj.pairing v v = u * π ^ e) :
    IsIModular R (formedSublattice L (R ∙ v)) (Ideal.span {π ^ e}) :=
  isIModular_span_singleton_pow R (formedSublattice L (R ∙ v))
    (formedSublatticeSpanSingletonBasis L v hne) π u e hπ
    (by rw [pairing_formedSublattice_spanSingletonBasis, hvv])

end Component

section Existence

variable [IsDiscreteValuationRing R] [Invertible (2 : R)]

/-- Over a discrete valuation ring with `2` invertible, a lattice with nonzero scale has a
rank-one modular orthogonal direct summand.

The vector of maximal scale spans a `π ^ e`-modular line, and the lattice is the direct sum
of that line and its orthogonal complement. This is the first step of the Jordan
decomposition. -/
theorem exists_isIModular_component (L : IntegralLatticeCat R) (hL : scaleIdeal L ≠ ⊥)
    (π : R) (hπ : Irreducible π) :
    ∃ (v : L.obj.carrier) (hproj : Module.Projective R ↥(R ∙ v)) (e : ℕ),
      IsCompl (R ∙ v) (orthogonalSubmodule L (R ∙ v)) ∧
        letI := hproj
        IsIModular R (formedSublattice L (R ∙ v)) (Ideal.span {π ^ e}) := by
  obtain ⟨v, hv, hcompl⟩ := exists_generatesScale_isCompl L hL
  have hne : L.obj.pairing v v ≠ 0 := fun h0 ↦
    hL (hv.trans (Ideal.span_singleton_eq_bot.mpr h0))
  obtain ⟨e, u, hvv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπ
  letI : Module.Free R ↥(R ∙ v) := Module.Free.of_basis (spanSingletonBasis L v hne)
  exact ⟨v, inferInstance, e, hcompl,
    isIModular_formedSublattice_span_singleton L v hne π u e hπ.ne_zero hvv⟩

end Existence

end LeanCategories.Lattices.Valued
