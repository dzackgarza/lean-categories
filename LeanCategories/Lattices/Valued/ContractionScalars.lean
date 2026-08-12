/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CliffordCenter
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

open CliffordAlgebra

namespace LeanCategories.Lattices.Valued

universe u v w

section Monomials

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A contraction kills a wedge product of vectors that the functional annihilates. -/
theorem contractLeft_ιMulti_of_forall_eq_zero {n : ℕ} (d : Module.Dual R M) (v : Fin n → M)
    (hv : ∀ k, d (v k) = 0) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R n v) = 0 := by
  induction n with
  | zero => rw [ExteriorAlgebra.ιMulti_zero_apply, contractLeft_one]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, hv 0, zero_smul,
      ih (Matrix.vecTail v) fun k => hv k.succ, mul_zero, sub_zero]

variable {I : Type w} [LinearOrder I] (b : Module.Basis I R M)

/-- The exterior monomial on the empty index set is `1`. -/
theorem basis_exteriorAlgebra_empty : b.ExteriorAlgebra (∅ : Finset I) = 1 := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_empty (α := I))]
  exact ExteriorAlgebra.ιMulti_zero_apply _

/-- The exterior monomial on a singleton is the image of the basis vector. -/
theorem basis_exteriorAlgebra_singleton (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton i)]
  have h0 : Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_singleton i)) 0 = i := by
    simp [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  simp [ExteriorAlgebra.ιMulti_family, h0]

/-- Contraction along a coordinate outside `S` kills the exterior monomial on `S`. -/
theorem contractLeft_coord_basis_of_notMem {i : I} {S : Finset I} (hi : i ∉ S) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra S) = 0 := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : S.card = S.card)]
  refine contractLeft_ιMulti_of_forall_eq_zero _ _ fun k => ?_
  have hmem := Finset.orderEmbOfFin_mem S (rfl : S.card = S.card) k
  have hne : Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (rfl : S.card = S.card)) k ≠ i := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact fun h => hi (h ▸ hmem)
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, hne]

/-- An exterior monomial splits, up to sign, as a basis vector times the monomial on the
remaining indices. -/
theorem exists_ι_mul_basis_erase {i : I} {S : Finset I} (hi : i ∈ S) :
    ∃ ε : ℤˣ, ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra (S.erase i)
      = ε • b.ExteriorAlgebra S := by
  classical
  set s : Set.powersetCard I 1 := Set.powersetCard.ofCard (Finset.card_singleton i) with hs
  set t : Set.powersetCard I (S.erase i).card :=
    Set.powersetCard.ofCard (rfl : (S.erase i).card = (S.erase i).card) with ht
  have hsv : (s : Finset I) = {i} := rfl
  have htv : (t : Finset I) = S.erase i := rfl
  have hdisj : Disjoint (s : Finset I) (t : Finset I) := by
    rw [hsv, htv, Finset.disjoint_left]
    simp
  have hunion : ((Set.powersetCard.disjUnion hdisj : Set.powersetCard I _) : Finset I) = S := by
    rw [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union, hsv, htv,
      Finset.singleton_union, Finset.insert_erase hi]
  have hmul := ExteriorAlgebra.basis_mul_of_disjoint b s t hdisj
  rw [hunion, hsv, htv] at hmul
  exact ⟨_, by rw [← basis_exteriorAlgebra_singleton b i]; exact hmul⟩

/-- Contraction along a coordinate of `S` sends the exterior monomial on `S` to a unit multiple
of the monomial on `S` with that index removed.

Together with `contractLeft_coord_basis_of_notMem` this computes `CliffordAlgebra.contractLeft`
on the exterior monomial basis `Module.Basis.ExteriorAlgebra`. -/
theorem contractLeft_coord_basis_of_mem {i : I} {S : Finset I} (hi : i ∈ S) :
    ∃ u : Rˣ, contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra S)
      = (u : R) • b.ExteriorAlgebra (S.erase i) := by
  classical
  obtain ⟨ε, hε⟩ := exists_ι_mul_basis_erase b hi
  have hsplit : contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)
      (ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra (S.erase i))
      = b.ExteriorAlgebra (S.erase i) := by
    rw [contractLeft_ι_mul, contractLeft_coord_basis_of_notMem b (Finset.notMem_erase i S),
      mul_zero, sub_zero, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, one_smul]
  rw [hε, Units.smul_def, map_zsmul, ← Int.cast_smul_eq_zsmul R] at hsplit
  have hwv : ((Units.map (Int.castRingHom R).toMonoidHom ε : Rˣ) : R) = ((ε : ℤ) : R) := rfl
  refine ⟨(Units.map (Int.castRingHom R).toMonoidHom ε)⁻¹, ?_⟩
  rw [← hsplit, ← hwv, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

end Monomials

section Field

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
variable {I : Type w} [LinearOrder I]

/-- The exterior monomial coefficients of positive degree all vanish for an element killed by
every contraction. -/
theorem basis_repr_eq_zero_of_forall_contractLeft (b : Module.Basis I K V)
    {z : ExteriorAlgebra K V}
    (hz : ∀ d : Module.Dual K V, contractLeft (Q := (0 : QuadraticForm K V)) d z = 0)
    {T : Finset I} (hT : T ≠ ∅) : b.ExteriorAlgebra.repr z T = 0 := by
  classical
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  obtain ⟨u, hu⟩ := contractLeft_coord_basis_of_mem b hi
  have hmap : (b.ExteriorAlgebra.coord (T.erase i)).comp
      (contractLeft (Q := (0 : QuadraticForm K V)) (b.coord i))
      = (u : K) • b.ExteriorAlgebra.coord T := by
    refine b.ExteriorAlgebra.ext fun S => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply, smul_eq_mul]
    by_cases hST : S = T
    · subst hST
      rw [hu]
      simp [Module.Basis.repr_self]
    · rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hST), mul_zero]
      by_cases hiS : i ∈ S
      · obtain ⟨v, hv⟩ := contractLeft_coord_basis_of_mem b hiS
        have hne : S.erase i ≠ T.erase i := fun h =>
          hST (by rw [← Finset.insert_erase hiS, h, Finset.insert_erase hi])
        rw [hv]
        simp [Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hne)]
      · rw [contractLeft_coord_basis_of_notMem b hiS, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h0 := LinearMap.congr_fun hmap z
  simp only [LinearMap.coe_comp, Function.comp_apply, hz, map_zero, LinearMap.smul_apply,
    Module.Basis.coord_apply, smul_eq_mul] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left u.ne_zero

/-- In the exterior algebra of a finite-dimensional space, an element killed by every
contraction is a scalar. -/
theorem exteriorAlgebra_exists_algebraMap [FiniteDimensional K V] {z : ExteriorAlgebra K V}
    (hz : ∀ d : Module.Dual K V, contractLeft (Q := (0 : QuadraticForm K V)) d z = 0) :
    ∃ r : K, z = algebraMap K (ExteriorAlgebra K V) r := by
  classical
  refine ⟨(Module.finBasis K V).ExteriorAlgebra.repr z ∅, ?_⟩
  have hsum := (Module.finBasis K V).ExteriorAlgebra.sum_repr z
  rw [Finset.sum_eq_single (∅ : Finset (Fin (Module.finrank K V))),
    basis_exteriorAlgebra_empty] at hsum
  · rw [Algebra.algebraMap_eq_smul_one]
    exact hsum.symm
  · exact fun T _ hT => by rw [basis_repr_eq_zero_of_forall_contractLeft _ hz hT, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- Contractions detect scalars in the Clifford algebra of a finite-dimensional space.

This discharges the classical hypothesis `ContractionsDetectScalars` isolated in
`LeanCategories.Lattices.Valued.CliffordCenter`. -/
theorem contractionsDetectScalars (Q : QuadraticForm K V) [Invertible (2 : K)]
    [FiniteDimensional K V] : ContractionsDetectScalars Q := by
  intro z hz
  have h := CliffordAlgebra.changeForm.associated_neg_proof (Q := Q)
  have hz' : ∀ d : Module.Dual K V,
      contractLeft (Q := (0 : QuadraticForm K V)) d (CliffordAlgebra.changeFormEquiv h z) = 0 := by
    intro d
    rw [CliffordAlgebra.changeFormEquiv_apply, ← CliffordAlgebra.changeForm_contractLeft h d z,
      hz d, map_zero]
  obtain ⟨r, hr⟩ := exteriorAlgebra_exists_algebraMap hz'
  refine ⟨r, ?_⟩
  have hsymm := congrArg (CliffordAlgebra.changeFormEquiv h).symm hr
  rw [LinearEquiv.symm_apply_apply, CliffordAlgebra.changeFormEquiv_symm,
    CliffordAlgebra.changeFormEquiv_apply, CliffordAlgebra.changeForm_algebraMap] at hsymm
  exact hsymm

end Field

end LeanCategories.Lattices.Valued
