/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.JordanComponent

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

section Projectivity

omit [IsDomain R] in
/-- The orthogonal complement of a complemented sublattice is projective.

It is a direct summand of the projective carrier, split by the projection along `P`. -/
theorem projective_orthogonalSubmodule_of_isCompl (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier)
    (h : IsCompl P (orthogonalSubmodule L P)) :
    Module.Projective R ↥(orthogonalSubmodule L P) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  exact Module.Projective.of_split (orthogonalSubmodule L P).subtype
    (Submodule.projectionOnto _ _ h.symm)
    (LinearMap.ext fun x ↦ Submodule.projectionOnto_apply_left h.symm x)

end Projectivity

section Splitting

variable (L : IntegralLatticeCat R) (P : Submodule R L.obj.carrier)
  [Module.Projective R P] [Module.Projective R ↥(orthogonalSubmodule L P)]

omit [IsDomain R] [Module.Projective R P]
  [Module.Projective R ↥(orthogonalSubmodule L P)] in
/-- Addition from a sublattice and its orthogonal complement is bijective when they are
complementary submodules. -/
theorem sublatticeOrthogonalSumLinearMap_bijective
    (h : IsCompl P (orthogonalSubmodule L P)) :
    Function.Bijective (sublatticeOrthogonalSumLinearMap L P) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    have hd : Disjoint (LinearMap.range P.subtype)
        (LinearMap.range (orthogonalSubmodule L P).subtype) := by
      simpa only [Submodule.range_subtype] using h.disjoint
    change LinearMap.ker
      (LinearMap.coprod P.subtype (orthogonalSubmodule L P).subtype) = ⊥
    rw [LinearMap.ker_coprod_of_disjoint_range _ _ hd]
    simp
  · rw [← LinearMap.range_eq_top, range_sublatticeOrthogonalSumLinearMap]
    exact h.sup_eq_top

/-- The carrier equivalence between the orthogonal sum and the ambient lattice. -/
noncomputable def sublatticeOrthogonalSumLinearEquiv
    (h : IsCompl P (orthogonalSubmodule L P)) :
    (orthogonalSum (formedSublattice L P) (orthogonalComplement L P)).obj.carrier ≃ₗ[R]
      L.obj.carrier :=
  LinearEquiv.ofBijective (sublatticeOrthogonalSumLinearMap L P)
    (sublatticeOrthogonalSumLinearMap_bijective L P h)

/-- A complemented sublattice and its orthogonal complement decompose the lattice.

The orthogonal sum of the two sublattices is isomorphic to the ambient lattice by the
addition map. -/
noncomputable def sublatticeOrthogonalSumIso
    (h : IsCompl P (orthogonalSubmodule L P)) :
    orthogonalSum (formedSublattice L P) (orthogonalComplement L P) ≅ L :=
  ObjectProperty.isoMk (P := isLattice R R)
    (BilinModuleCat.isoMk (sublatticeOrthogonalSumLinearEquiv L P h)
      (BilinModuleCat.map_pairing (sublatticeOrthogonalSumInclusion L P).hom))

omit [IsDomain R] in
@[simp]
theorem sublatticeOrthogonalSumIso_hom (h : IsCompl P (orthogonalSubmodule L P)) :
    (sublatticeOrthogonalSumIso L P h).hom = sublatticeOrthogonalSumInclusion L P :=
  rfl

omit [IsDomain R] in
/-- The orthogonal-sum inclusion is an isomorphism of lattices when the sublattice and its
orthogonal complement are complementary submodules. -/
theorem sublatticeOrthogonalSumIsIso (h : IsCompl P (orthogonalSubmodule L P)) :
    IsIso (sublatticeOrthogonalSumInclusion L P) := by
  rw [← sublatticeOrthogonalSumIso_hom L P h]
  infer_instance

end Splitting

section Rank

/-- Ranks add across an orthogonal splitting of a lattice. -/
theorem finrank_orthogonalSubmodule_add (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier)
    [Module.Free R P] [Module.Finite R P]
    [Module.Free R ↥(orthogonalSubmodule L P)]
    [Module.Finite R ↥(orthogonalSubmodule L P)]
    (h : IsCompl P (orthogonalSubmodule L P)) :
    Module.finrank R P + Module.finrank R ↥(orthogonalSubmodule L P)
      = Module.finrank R L.obj.carrier := by
  rw [← Module.finrank_prod]
  exact (Submodule.prodEquivOfIsCompl P _ h).finrank_eq

end Rank

section Decomposition

variable [IsDiscreteValuationRing R] [Invertible (2 : R)]

/-- Over a discrete valuation ring with `2` invertible, a finite lattice with nonzero scale
splits off a rank-one modular line.

The lattice is isomorphic to the orthogonal sum of a `π ^ e`-modular line and its orthogonal
complement, whose rank is one less. The line carries the whole scale of `L`, so `e` is the
scale exponent of `L`. This is the statement a Jordan induction consumes. -/
theorem exists_orthogonal_decomposition (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (hL : scaleIdeal L ≠ ⊥)
    (π : R) (hπ : Irreducible π) :
    ∃ (v : L.obj.carrier) (e : ℕ) (hline : Module.Projective R ↥(R ∙ v))
      (hperp : Module.Projective R ↥(orthogonalSubmodule L (R ∙ v))),
      letI := hline
      letI := hperp
      scaleIdeal L = Ideal.span {π ^ e} ∧
        IsIModular R (formedSublattice L (R ∙ v)) (Ideal.span {π ^ e}) ∧
          Module.finrank R ↥(orthogonalSubmodule L (R ∙ v)) + 1
              = Module.finrank R L.obj.carrier ∧
            IsCompl (R ∙ v) (orthogonalSubmodule L (R ∙ v)) := by
  obtain ⟨v, hv, hcompl⟩ := exists_generatesScale_isCompl L hL
  have hne : L.obj.pairing v v ≠ 0 := fun h0 ↦
    hL (hv.trans (Ideal.span_singleton_eq_bot.mpr h0))
  obtain ⟨e, u, hvv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπ
  letI hbasis : Module.Basis (Fin 1) R ↥(R ∙ v) := spanSingletonBasis L v hne
  letI : Module.Free R ↥(R ∙ v) := Module.Free.of_basis hbasis
  letI : Module.Finite R ↥(R ∙ v) := Module.Finite.of_basis hbasis
  letI : Module.Projective R ↥(orthogonalSubmodule L (R ∙ v)) :=
    projective_orthogonalSubmodule_of_isCompl L (R ∙ v) hcompl
  letI : Module.Free R ↥(orthogonalSubmodule L (R ∙ v)) :=
    Module.free_of_flat_of_isLocalRing
  refine ⟨v, e, inferInstance, inferInstance, ?_,
    isIModular_formedSublattice_span_singleton L v hne π u e hπ.ne_zero hvv, ?_, hcompl⟩
  · rw [hv, hvv, Ideal.span_singleton_mul_left_unit u.isUnit]
  · rw [← finrank_orthogonalSubmodule_add L (R ∙ v) hcompl,
      Module.finrank_eq_card_basis hbasis]
    simp [add_comm]

end Decomposition

end LeanCategories.Lattices.Valued
