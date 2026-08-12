/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Discriminant
public import LeanCategories.Lattices.Valued.JordanRecursion

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

section ScaleOfSum

/-- An isomorphism transports every pairing value, so it can only shrink the scale. -/
theorem scaleModule_le_of_iso {L M : FiniteProjectiveLatticeCat R R} (e : L ≅ M) :
    scaleModule M.obj ≤ scaleModule L.obj := by
  rw [← isIIntegral_iff_scaleModule_le, isIIntegral_iff_pairing_mem]
  intro x y
  obtain ⟨a, rfl⟩ := (finiteProjectiveLatticeLinearEquiv e).surjective x
  obtain ⟨b, rfl⟩ := (finiteProjectiveLatticeLinearEquiv e).surjective y
  rw [finiteProjectiveLatticeLinearEquiv_pairing]
  exact pairing_mem_scaleModule L.obj a b

/-- The scale ideal is an isomorphism invariant of a lattice. -/
theorem scaleModule_eq_of_iso {L M : FiniteProjectiveLatticeCat R R} (e : L ≅ M) :
    scaleModule M.obj = scaleModule L.obj :=
  le_antisymm (scaleModule_le_of_iso e) (scaleModule_le_of_iso e.symm)

/-- A pair of vectors supported on one summand pairs inside that summand. -/
theorem pairing_indexedOrthogonalSum_single {n : ℕ}
    (D : Fin n → FiniteProjectiveLatticeCat R R) (i : Fin n)
    (u v : (D i).obj.obj.carrier) :
    (finiteProjectiveIndexedOrthogonalSum D).obj.obj.pairing (Pi.single i u) (Pi.single i v) =
      (D i).obj.obj.pairing u v := by
  let U : (j : Fin n) → (D j).obj.obj.carrier := Pi.single i u
  let V : (j : Fin n) → (D j).obj.obj.carrier := Pi.single i v
  change (∑ j, (D j).obj.obj.pairing (U j) (V j)) = _
  refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hj ↦ ?_).trans ?_
  · simp [U, V, hj]
  · simp [U, V]

/-- The scale of an indexed orthogonal sum is the supremum of the scales of the summands. -/
theorem scaleModule_finiteProjectiveIndexedOrthogonalSum {n : ℕ}
    (D : Fin n → FiniteProjectiveLatticeCat R R) :
    scaleModule (finiteProjectiveIndexedOrthogonalSum D).obj =
      ⨆ i, scaleModule (D i).obj := by
  refine le_antisymm ?_ (iSup_le fun i ↦ ?_)
  · rw [← isIIntegral_iff_scaleModule_le, isIIntegral_iff_pairing_mem]
    intro x y
    change (∑ i, (D i).obj.obj.pairing (x i) (y i)) ∈ _
    exact Submodule.sum_mem _ fun i _ ↦
      le_iSup (fun i ↦ scaleModule (D i).obj) i (pairing_mem_scaleModule (D i).obj (x i) (y i))
  · rw [← isIIntegral_iff_scaleModule_le, isIIntegral_iff_pairing_mem]
    intro x y
    rw [← pairing_indexedOrthogonalSum_single D i x y]
    exact pairing_mem_scaleModule _ _ _

end ScaleOfSum

section ModularIntegrality

variable [IsDomain R]

/-- A modular lattice is integral for its modularity ideal.

The lattice lies in its own metric dual, so every pairing value lies in the ideal. -/
theorem scaleModule_le_of_isIModular (L : IntegralLatticeCat R) (I : Ideal R)
    (hmod : IsIModular R L I) : scaleModule L ≤ I := by
  have hdual : fractionalIdealDual R L (integralFractionalIdeal R I) = integralImage R L :=
    hmod
  rw [← isIIntegral_iff_scaleModule_le, isIIntegral_iff_pairing_mem]
  intro x y
  refine (toRationalSpan_mem_idealDual_iff R L I x).mp ?_ y
  rw [idealDual, hdual]
  exact ⟨x, rfl⟩

end ModularIntegrality

section ModularScale

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- A modular lattice whose scale misses one power of the uniformizer is divisible by it.

Dividing a vector by the uniformizer stays in the metric dual, hence in the lattice. -/
theorem exists_smul_of_isIModular (L : IntegralLatticeCat R)
    (π : R) (hπ : Irreducible π) (e : ℕ)
    (hmod : IsIModular R L (Ideal.span {π ^ e}))
    (hs : scaleModule L ≤ Ideal.span {π ^ (e + 1)}) (x : L.obj.carrier) :
    ∃ w, x = π • w := by
  have hdual : fractionalIdealDual R L (integralFractionalIdeal R (Ideal.span {π ^ e}))
      = integralImage R L := hmod
  have hπ0 : algebraMap R (FractionRing R) π ≠ 0 := fun h ↦
    hπ.ne_zero ((FaithfulSMul.algebraMap_injective R (FractionRing R)) (by rw [h, map_zero]))
  have hz : (algebraMap R (FractionRing R) π)⁻¹ ⊗ₜ[R] x ∈
      fractionalIdealDual R L (integralFractionalIdeal R (Ideal.span {π ^ e})) := by
    rw [mem_fractionalIdealDual_iff]
    intro y
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hs (pairing_mem_scaleModule L x y))
    have hval : rationalizedForm R L ((algebraMap R (FractionRing R) π)⁻¹ ⊗ₜ[R] x)
        (toRationalSpan R L y) = algebraMap R (FractionRing R) (π ^ e * d) := by
      rw [toRationalSpan_apply, rationalizedForm_tmul, mul_one, hd,
        show π ^ (e + 1) * d = π * (π ^ e * d) by ring, map_mul, inv_mul_cancel_left₀ hπ0]
    rw [hval]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_span_singleton.mpr ⟨d, rfl⟩)
  rw [hdual] at hz
  obtain ⟨w, hw⟩ := hz
  have hmul := congrArg (fun t ↦ algebraMap R (FractionRing R) π • t) hw
  simp only [toRationalSpan_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    mul_inv_cancel₀ hπ0] at hmul
  refine ⟨w, toRationalSpan_injective R L ?_⟩
  rw [toRationalSpan_apply, toRationalSpan_apply, ← hmul, ← TensorProduct.smul_tmul,
    Algebra.smul_def, mul_one]

/-- A nonzero modular lattice has its modularity ideal as scale.

The scale is contained in the ideal because the lattice lies in its own metric dual. It is
not smaller: otherwise the lattice would be divisible by the uniformizer, hence zero. -/
theorem scaleModule_of_isIModular (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] [Nontrivial L.obj.carrier]
    (π : R) (hπ : Irreducible π) (e : ℕ)
    (hmod : IsIModular R L (Ideal.span {π ^ e})) :
    scaleModule L = Ideal.span {π ^ e} := by
  have hle : scaleModule L ≤ Ideal.span {π ^ e} := scaleModule_le_of_isIModular L _ hmod
  refine le_antisymm hle ?_
  by_contra hcon
  have hs : scaleModule L ≤ Ideal.span {π ^ (e + 1)} := by
    by_cases hbot : scaleModule L = ⊥
    · rw [hbot]
      exact bot_le
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hπ
    have hek : e ≤ k := (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).mp
      (Ideal.span_singleton_le_span_singleton.mp (hk ▸ hle))
    have hne : e ≠ k := by
      rintro rfl
      exact hcon (hk ▸ le_rfl)
    rw [hk]
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (by omega))
  have htop : (⊤ : Submodule R L.obj.carrier) ≤ Ideal.span {π} • ⊤ := by
    intro x _
    obtain ⟨w, rfl⟩ := exists_smul_of_isIModular L π hπ e hmod hs x
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) Submodule.mem_top
  have hjac : Ideal.span {π} ≤ (⊥ : Ideal R).jacobson := by
    rw [Ideal.span_le, Set.singleton_subset_iff,
      IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {π}) ⊤
    (Module.Finite.iff_fg.mp inferInstance) htop hjac
  obtain ⟨y, hy⟩ := exists_ne (0 : L.obj.carrier)
  exact hy ((Submodule.eq_bot_iff _).mp hbot y Submodule.mem_top)

end ModularScale

section Invariants

variable [IsDomain R] [IsDiscreteValuationRing R]
variable {L : FiniteProjectiveLatticeCat R R} {π : R} {n : ℕ}

/-- The rank of an indexed orthogonal sum is the sum of the ranks. -/
theorem rank_finiteProjectiveIndexedOrthogonalSum
    (D : Fin n → FiniteProjectiveLatticeCat R R) :
    (finiteProjectiveIndexedOrthogonalSum D).rank = ∑ i, (D i).rank := by
  letI (i : Fin n) : Module.Finite R (D i).obj.obj.carrier := (D i).property
  letI (i : Fin n) : Module.Free R (D i).obj.obj.carrier := (D i).carrier_free
  change Module.finrank R ((i : Fin n) → (D i).obj.obj.carrier) = _
  exact Module.finrank_pi_fintype R

namespace JordanDecomposition

/-- The multiset of exponent-rank pairs attached to a Jordan decomposition.

The components themselves are not canonical, but this data is expected to depend only on
the lattice. -/
noncomputable def invariants (J : JordanDecomposition L π n) : Multiset (ℕ × ℕ) :=
  Finset.univ.val.map fun i ↦ (J.exponent i, (J.component i).rank)

/-- The ranks recorded by a Jordan decomposition add up to the rank of the lattice. -/
theorem sum_rank_invariants (J : JordanDecomposition L π n) :
    ((J.invariants.map Prod.snd).sum : ℕ) = L.rank := by
  have h : (J.invariants.map Prod.snd).sum = ∑ i, (J.component i).rank := by
    rw [invariants, Multiset.map_map]
    rfl
  rw [h, ← rank_finiteProjectiveIndexedOrthogonalSum J.component]
  exact finiteProjective_rank_eq_of_iso R R J.decomposition

omit [IsDiscreteValuationRing R] in
/-- The scale of a lattice is inside the ideal of the smallest exponent of any Jordan
decomposition of it.

Every component pairs inside its own ideal, and the exponents increase. -/
theorem scaleModule_le (J : JordanDecomposition L π (n + 1)) :
    scaleModule L.obj ≤ Ideal.span {π ^ J.exponent 0} := by
  rw [scaleModule_eq_of_iso J.decomposition, scaleModule_finiteProjectiveIndexedOrthogonalSum]
  refine iSup_le fun i ↦ (scaleModule_le_of_isIModular _ _ (J.component_isModular i)).trans ?_
  exact Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow π (J.exponent_strictMono.monotone (Fin.zero_le i)))

/-- The smallest exponent of a Jordan decomposition is the scale exponent of the lattice.

This is the first invariant of the decomposition: the exponents increase strictly, so the
component of smallest exponent carries the whole scale of the lattice. Only that component
has to be nonzero. -/
theorem scaleModule_eq (J : JordanDecomposition L π (n + 1))
    (hne : Nontrivial (J.component 0).obj.obj.carrier) :
    scaleModule L.obj = Ideal.span {π ^ J.exponent 0} := by
  refine le_antisymm J.scaleModule_le ?_
  letI := hne
  letI : Module.Finite R (J.component 0).obj.obj.carrier := (J.component 0).property
  have h0 : scaleModule (J.component 0).obj = Ideal.span {π ^ J.exponent 0} :=
    scaleModule_of_isIModular (J.component 0).obj π J.uniformizer_isIrreducible
      (J.exponent 0) (J.component_isModular 0)
  rw [scaleModule_eq_of_iso J.decomposition, scaleModule_finiteProjectiveIndexedOrthogonalSum,
    ← h0]
  exact le_iSup (fun i ↦ scaleModule (J.component i).obj) 0

/-- A Jordan decomposition with one component records the exponent and the rank of the
lattice. -/
theorem invariants_of_single (J : JordanDecomposition L π 1) :
    J.invariants = {(J.exponent 0, L.rank)} := by
  have hrank : (J.component 0).rank = L.rank := by
    have h := J.sum_rank_invariants
    simpa [invariants] using h
  rw [invariants, ← hrank]
  rfl

end JordanDecomposition

/-- The smallest exponent is an invariant of the lattice.

Two Jordan decompositions of the same lattice, with possibly different uniformizers and
different numbers of components, record the same smallest exponent. -/
theorem exponent_zero_eq_of_jordanDecomposition {ϖ : R} {m : ℕ}
    (J : JordanDecomposition L π (n + 1)) (K : JordanDecomposition L ϖ (m + 1))
    (hJ : Nontrivial (J.component 0).obj.obj.carrier)
    (hK : Nontrivial (K.component 0).obj.obj.carrier) :
    J.exponent 0 = K.exponent 0 := by
  have hπ := J.uniformizer_isIrreducible
  have hspan : Ideal.span {π ^ J.exponent 0} = Ideal.span {ϖ ^ K.exponent 0} := by
    rw [← J.scaleModule_eq hJ, K.scaleModule_eq hK]
  have hassoc : Associated (π ^ J.exponent 0) (π ^ K.exponent 0) :=
    (Ideal.span_singleton_eq_span_singleton.mp hspan).trans
      (Associated.pow_pow (IsDiscreteValuationRing.associated_of_irreducible R hπ
        K.uniformizer_isIrreducible)).symm
  have hle : J.exponent 0 ≤ K.exponent 0 :=
    (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).mp hassoc.dvd
  have hge : K.exponent 0 ≤ J.exponent 0 :=
    (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).mp hassoc.symm.dvd
  omega

/-- Two one-component Jordan decompositions of a lattice record the same invariants.

This is the uniqueness statement for a single Jordan component: the exponent is the scale
exponent and the rank is the rank of the lattice, so neither depends on the decomposition
or on the uniformizer. -/
theorem invariants_eq_of_single {ϖ : R} (J : JordanDecomposition L π 1)
    (K : JordanDecomposition L ϖ 1)
    (hJ : Nontrivial (J.component 0).obj.obj.carrier)
    (hK : Nontrivial (K.component 0).obj.obj.carrier) :
    J.invariants = K.invariants := by
  rw [J.invariants_of_single, K.invariants_of_single,
    exponent_zero_eq_of_jordanDecomposition J K hJ hK]

/-- The total rank recorded by a Jordan decomposition is an invariant of the lattice. -/
theorem sum_rank_invariants_eq {ϖ : R} {m : ℕ}
    (J : JordanDecomposition L π n) (K : JordanDecomposition L ϖ m) :
    ((J.invariants.map Prod.snd).sum : ℕ) = (K.invariants.map Prod.snd).sum := by
  rw [J.sum_rank_invariants, K.sum_rank_invariants]

end Invariants

end LeanCategories.Lattices.Valued
