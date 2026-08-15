/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.JordanInvariants
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.QuotSMulTop

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued
open scoped Pointwise

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

section Layer

/-- The layer of a lattice at an ideal: the vectors pairing into `I` with the whole lattice.

This is the intersection of the preimages of `I` under the linear forms `x ↦ b(x, y)`. -/
def layerSubmodule (L : IntegralLatticeCat R) (I : Ideal R) : Submodule R L.obj.carrier :=
  ⨅ y : L.obj.carrier, Submodule.comap (L.obj.bilinMap.flip y) I

@[simp]
theorem mem_layerSubmodule_iff (L : IntegralLatticeCat R) (I : Ideal R) (x : L.obj.carrier) :
    x ∈ layerSubmodule L I ↔ ∀ y, L.obj.pairing x y ∈ I := by
  simp [layerSubmodule]

/-- A lattice whose scale is inside `I` is its own layer at `I`. -/
theorem layerSubmodule_eq_top_of_scaleIdeal_le (L : IntegralLatticeCat R) (I : Ideal R)
    (h : scaleIdeal L ≤ I) : layerSubmodule L I = ⊤ :=
  eq_top_iff.mpr fun x _ ↦
    (mem_layerSubmodule_iff L I x).mpr fun y ↦ h (pairing_mem_scaleIdeal L x y)

end Layer

section LayerOfSum

variable {n : ℕ}

/-- Pairing against a vector supported on one summand only sees that summand. -/
theorem pairing_indexedOrthogonalSum_single_right
    (D : Fin n → FiniteProjectiveLatticeCat R R) (i : Fin n)
    (x : (finiteProjectiveIndexedOrthogonalSum D).obj.obj.carrier)
    (v : (D i).obj.obj.carrier) :
    (finiteProjectiveIndexedOrthogonalSum D).obj.obj.pairing x (Pi.single i v) =
      (D i).obj.obj.pairing (x i) v := by
  let X : (j : Fin n) → (D j).obj.obj.carrier := x
  let V : (j : Fin n) → (D j).obj.obj.carrier := Pi.single i v
  change (∑ j, (D j).obj.obj.pairing (X j) (V j)) = _
  refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hj ↦ ?_).trans ?_
  · simp [V, hj]
  · simp [X, V]

/-- The layer of an orthogonal sum is the product of the layers of the summands. -/
theorem layerSubmodule_finiteProjectiveIndexedOrthogonalSum
    (D : Fin n → FiniteProjectiveLatticeCat R R) (I : Ideal R) :
    layerSubmodule (finiteProjectiveIndexedOrthogonalSum D).obj I =
      Submodule.pi Set.univ fun i ↦ layerSubmodule (D i).obj I := by
  refine Submodule.ext fun x ↦ (mem_layerSubmodule_iff _ I x).trans ?_
  refine ⟨fun h ↦ Submodule.mem_pi.mpr fun i _ ↦ ?_, fun hpi y ↦ ?_⟩
  · refine (mem_layerSubmodule_iff (D i).obj I (x i)).mpr fun v ↦ ?_
    rw [← pairing_indexedOrthogonalSum_single_right D i x v]
    exact h (Pi.single i v)
  · have h : ∀ i, x i ∈ layerSubmodule (D i).obj I := fun i ↦
      Submodule.mem_pi.mp hpi i (Set.mem_univ i)
    let X : (j : Fin n) → (D j).obj.obj.carrier := x
    let Y : (j : Fin n) → (D j).obj.obj.carrier := y
    change (∑ j, (D j).obj.obj.pairing (X j) (Y j)) ∈ I
    exact Submodule.sum_mem _ fun j _ ↦
      (mem_layerSubmodule_iff (D j).obj I (X j)).mp (h j) (Y j)

/-- The layer of a binary orthogonal sum is the product of the layers of the summands. -/
theorem layerSubmodule_finiteProjectiveOrthogonalSum (A B : FiniteProjectiveLatticeCat R R)
    (I : Ideal R) :
    layerSubmodule (finiteProjectiveOrthogonalSum A B).obj I =
      (layerSubmodule A.obj I).prod (layerSubmodule B.obj I) := by
  refine Submodule.ext fun x ↦ (mem_layerSubmodule_iff _ I x).trans ?_
  refine ⟨fun h ↦ Submodule.mem_prod.mpr ⟨?_, ?_⟩, fun hp y ↦ ?_⟩
  · refine (mem_layerSubmodule_iff A.obj I x.1).mpr fun u ↦ ?_
    have hu := h ((u, 0) : A.obj.obj.carrier × B.obj.obj.carrier)
    change A.obj.obj.pairing x.1 u + B.obj.obj.pairing x.2 0 ∈ I at hu
    simpa using hu
  · refine (mem_layerSubmodule_iff B.obj I x.2).mpr fun v ↦ ?_
    have hv := h ((0, v) : A.obj.obj.carrier × B.obj.obj.carrier)
    change A.obj.obj.pairing x.1 0 + B.obj.obj.pairing x.2 v ∈ I at hv
    simpa using hv
  · change A.obj.obj.pairing x.1 y.1 + B.obj.obj.pairing x.2 y.2 ∈ I
    exact I.add_mem ((mem_layerSubmodule_iff A.obj I x.1).mp (Submodule.mem_prod.mp hp).1 y.1)
      ((mem_layerSubmodule_iff B.obj I x.2).mp (Submodule.mem_prod.mp hp).2 y.2)

/-- Layers are transported by isometries of lattices. -/
theorem layerSubmodule_map_of_iso {L M : FiniteProjectiveLatticeCat R R} (e : L ≅ M)
    (I : Ideal R) :
    Submodule.map (finiteProjectiveLatticeLinearEquiv e).toLinearMap (layerSubmodule L.obj I) =
      layerSubmodule M.obj I := by
  refine Submodule.ext fun y ↦ ?_
  rw [Submodule.mem_map_equiv, mem_layerSubmodule_iff, mem_layerSubmodule_iff]
  constructor
  · intro h z
    have hz := h ((finiteProjectiveLatticeLinearEquiv e).symm z)
    rwa [← finiteProjectiveLatticeLinearEquiv_pairing e, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at hz
  · intro h x
    have hx := h (finiteProjectiveLatticeLinearEquiv e x)
    rwa [← LinearEquiv.apply_symm_apply (finiteProjectiveLatticeLinearEquiv e) y,
      finiteProjectiveLatticeLinearEquiv_pairing] at hx

end LayerOfSum

section LayerOfModular

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- A vector of a modular lattice pairing one power deeper is divisible by the uniformizer.

This is the pointwise form of `exists_smul_of_isIModular`: only the pairings of the given
vector are constrained. Dividing the vector by the uniformizer keeps it in the metric dual,
hence in the lattice. -/
theorem exists_smul_of_mem_layerSubmodule (L : IntegralLatticeCat R)
    (π : R) (hπ : Irreducible π) (e : ℕ)
    (hmod : IsIModular R L (Ideal.span {π ^ e})) {x : L.obj.carrier}
    (hx : x ∈ layerSubmodule L (Ideal.span {π ^ (e + 1)})) :
    ∃ w, x = π • w := by
  have hdual : fractionalIdealDual R L (integralFractionalIdeal R (Ideal.span {π ^ e}))
      = integralImage R L := hmod
  have hπ0 : algebraMap R (FractionRing R) π ≠ 0 := fun h ↦
    hπ.ne_zero ((FaithfulSMul.algebraMap_injective R (FractionRing R)) (by rw [h, map_zero]))
  have hz : (algebraMap R (FractionRing R) π)⁻¹ ⊗ₜ[R] x ∈
      fractionalIdealDual R L (integralFractionalIdeal R (Ideal.span {π ^ e})) := by
    rw [mem_fractionalIdealDual_iff]
    intro y
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp ((mem_layerSubmodule_iff L _ x).mp hx y)
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

/-- The layer of a `π ^ e`-modular lattice one power deeper is the uniformizer multiple.

This is the step that recovers the rank of a Jordan component: the quotient of a modular
lattice by this layer is the quotient by the uniformizer. -/
theorem layerSubmodule_of_isIModular (L : IntegralLatticeCat R)
    (π : R) (hπ : Irreducible π) (e : ℕ)
    (hmod : IsIModular R L (Ideal.span {π ^ e})) :
    layerSubmodule L (Ideal.span {π ^ (e + 1)}) = π • (⊤ : Submodule R L.obj.carrier) := by
  rw [← Submodule.ideal_span_singleton_smul]
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.smul_le.mpr fun r hr m _ ↦ ?_)
  · obtain ⟨w, rfl⟩ := exists_smul_of_mem_layerSubmodule L π hπ e hmod hx
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) Submodule.mem_top
  · refine (mem_layerSubmodule_iff L _ _).mpr fun y ↦ ?_
    rw [BilinModuleCat.pairing_smul_left, smul_eq_mul, Ideal.mem_span_singleton, pow_succ']
    exact mul_dvd_mul (Ideal.mem_span_singleton.mp hr)
      (Ideal.mem_span_singleton.mp (scaleIdeal_le_of_isIModular L _ hmod
        (pairing_mem_scaleIdeal L m y)))

end LayerOfModular

section Residue

variable [IsDomain R] [IsDiscreteValuationRing R]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The residue ring of a uniformizer is not the zero ring. -/
theorem nontrivial_quotient_span_singleton {π : R} (hπ : Irreducible π) :
    Nontrivial (R ⧸ Ideal.span {π}) :=
  Ideal.Quotient.nontrivial_iff.mpr fun h ↦
    hπ.not_isUnit (Ideal.span_singleton_eq_top.mp h)

/-- Reducing a finite free module modulo a uniformizer keeps its dimension.

The reduction is the base change to the residue ring, so its dimension over the residue ring
is the rank of the module. -/
theorem finrank_quotSMulTop {π : R} (hπ : Irreducible π) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Free R M] :
    Module.finrank (R ⧸ Ideal.span {π}) (QuotSMulTop π M) = Module.finrank R M := by
  haveI := nontrivial_quotient_span_singleton hπ
  haveI : IsScalarTower R (R ⧸ Ideal.span {π}) (QuotSMulTop π M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have e : QuotSMulTop π M ≃ₗ[R ⧸ Ideal.span {π}] TensorProduct R (R ⧸ Ideal.span {π}) M :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (QuotSMulTop.equivQuotTensor π M)
  rw [e.finrank_eq, Module.finrank_baseChange]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Dividing a product by a uniformizer multiple of the first factor and the whole second
factor leaves the reduction of the first factor. -/
noncomputable def prodQuotSMulTopEquiv (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (π : R) :
    ((M × N) ⧸ (π • (⊤ : Submodule R M)).prod (⊤ : Submodule R N)) ≃ₗ[R] QuotSMulTop π M := by
  have hker : LinearMap.ker
      ((Submodule.mkQ (π • (⊤ : Submodule R M))).comp (LinearMap.fst R M N)) =
      (π • (⊤ : Submodule R M)).prod (⊤ : Submodule R N) := by
    refine Submodule.ext fun x ↦ ?_
    rw [LinearMap.mem_ker, Submodule.mem_prod]
    change Submodule.Quotient.mk x.1 = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun h ↦ ⟨h, Submodule.mem_top⟩, fun h ↦ h.1⟩
  have hsurj : Function.Surjective
      ((Submodule.mkQ (π • (⊤ : Submodule R M))).comp (LinearMap.fst R M N)) := fun y ↦ by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (π • (⊤ : Submodule R M)) y
    exact ⟨(a, 0), rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ hsurj)

end Residue

section JordanLayer

variable [IsDomain R] [IsDiscreteValuationRing R]
variable {L : FiniteProjectiveLatticeCat R R} {π : R} {n : ℕ}

namespace JordanDecomposition

omit [IsDiscreteValuationRing R] in
/-- The components above the first pair one power deeper than the smallest exponent. -/
theorem scaleIdeal_tail_le (J : JordanDecomposition L π (n + 1)) :
    scaleIdeal (finiteProjectiveIndexedOrthogonalSum
        fun i : Fin n ↦ J.component i.succ).obj ≤
      Ideal.span {π ^ (J.exponent 0 + 1)} := by
  rw [scaleIdeal_finiteProjectiveIndexedOrthogonalSum]
  refine iSup_le fun i ↦
    (scaleIdeal_le_of_isIModular _ _ (J.component_isModular i.succ)).trans ?_
  exact Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow π (J.exponent_strictMono (Fin.succ_pos i)))

/-- The layer of the split lattice keeps only the uniformizer multiples of the first
component.

Every other component pairs one power deeper than the smallest exponent, so it lies inside
the layer as a whole. -/
theorem layerSubmodule_split_eq (J : JordanDecomposition L π (n + 1)) :
    layerSubmodule (finiteProjectiveOrthogonalSum (J.component 0)
          (finiteProjectiveIndexedOrthogonalSum fun i : Fin n ↦ J.component i.succ)).obj
        (Ideal.span {π ^ (J.exponent 0 + 1)}) =
      (π • (⊤ : Submodule R (J.component 0).obj.obj.carrier)).prod ⊤ := by
  rw [layerSubmodule_finiteProjectiveOrthogonalSum,
    layerSubmodule_of_isIModular _ π J.uniformizer_isIrreducible _ (J.component_isModular 0),
    layerSubmodule_eq_top_of_scaleIdeal_le _ _ J.scaleIdeal_tail_le]

/-- The quotient of the lattice by its layer is the residue reduction of the smallest
Jordan component.

The layer keeps the uniformizer multiples of the smallest component and all the other
components, so only the first component survives, reduced modulo the uniformizer. -/
noncomputable def quotientLayerEquiv (J : JordanDecomposition L π (n + 1)) :
    (L.obj.obj.carrier ⧸ layerSubmodule L.obj (Ideal.span {π ^ (J.exponent 0 + 1)})) ≃ₗ[R]
      QuotSMulTop π (J.component 0).obj.obj.carrier :=
  let f : finiteProjectiveOrthogonalSum (J.component 0)
      (finiteProjectiveIndexedOrthogonalSum fun i : Fin n ↦ J.component i.succ) ≅ L :=
    (finiteProjectiveIndexedOrthogonalSumConsIso J.component).symm ≪≫ J.decomposition
  (Submodule.Quotient.equiv _ _ (finiteProjectiveLatticeLinearEquiv f)
        (layerSubmodule_map_of_iso f _)).symm.trans
    ((Submodule.quotEquivOfEq _ _ J.layerSubmodule_split_eq).trans
      (prodQuotSMulTopEquiv _ _ π))

/-- The residue dimension of the reduced smallest component is its rank. -/
theorem finrank_quotSMulTop_component_zero (J : JordanDecomposition L π (n + 1)) :
    Module.finrank (R ⧸ Ideal.span {π})
        (QuotSMulTop π (J.component 0).obj.obj.carrier) =
      (J.component 0).rank := by
  letI : Module.Free R (J.component 0).obj.obj.carrier := (J.component 0).carrier_free
  exact finrank_quotSMulTop J.uniformizer_isIrreducible _

end JordanDecomposition

/-- The rank of the smallest Jordan component is an invariant of the lattice.

Both decompositions compute the same quotient of the lattice by the same layer, and that
quotient is the smallest component reduced modulo the uniformizer. -/
theorem rank_component_zero_eq_of_jordanDecomposition {ϖ : R} {m : ℕ}
    (J : JordanDecomposition L π (n + 1)) (K : JordanDecomposition L ϖ (m + 1)) :
    (J.component 0).rank = (K.component 0).rank := by
  have hassoc : Associated π ϖ := IsDiscreteValuationRing.associated_of_irreducible R
    J.uniformizer_isIrreducible K.uniformizer_isIrreducible
  have hπϖ : Ideal.span {ϖ} = Ideal.span {π} :=
    Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm
  have hspan : Ideal.span {π ^ (J.exponent 0 + 1)} = Ideal.span {ϖ ^ (K.exponent 0 + 1)} := by
    rw [exponent_zero_eq_of_jordanDecomposition J K]
    exact Ideal.span_singleton_eq_span_singleton.mpr (Associated.pow_pow hassoc)
  have hsmul : ϖ • (⊤ : Submodule R (K.component 0).obj.obj.carrier) = π • ⊤ := by
    rw [← Submodule.ideal_span_singleton_smul, ← Submodule.ideal_span_singleton_smul, hπϖ]
  have hR : QuotSMulTop π (J.component 0).obj.obj.carrier ≃ₗ[R]
      QuotSMulTop π (K.component 0).obj.obj.carrier :=
    J.quotientLayerEquiv.symm.trans
      (((Submodule.quotEquivOfEq _ _ (congrArg (layerSubmodule L.obj) hspan)).trans
        K.quotientLayerEquiv).trans (Submodule.quotEquivOfEq _ _ hsmul))
  haveI := nontrivial_quotient_span_singleton J.uniformizer_isIrreducible
  haveI : IsScalarTower R (R ⧸ Ideal.span {π})
      (QuotSMulTop π (J.component 0).obj.obj.carrier) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  haveI : IsScalarTower R (R ⧸ Ideal.span {π})
      (QuotSMulTop π (K.component 0).obj.obj.carrier) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hfin := (LinearEquiv.extendScalarsOfSurjective (S := R ⧸ Ideal.span {π})
    Ideal.Quotient.mk_surjective hR).finrank_eq
  rw [J.finrank_quotSMulTop_component_zero] at hfin
  letI : Module.Free R (K.component 0).obj.obj.carrier := (K.component 0).carrier_free
  rw [finrank_quotSMulTop J.uniformizer_isIrreducible] at hfin
  exact hfin

end JordanLayer

end LeanCategories.Lattices.Valued
