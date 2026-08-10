/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.BaseChange
public import LeanCategories.Lattices.Valued.Constructions
public import LeanCategories.Lattices.Valued.ScaleAndEvenness
public import Mathlib.CategoryTheory.Core
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [LinearOrder K]

/-- The quadratic form associated to a finite symmetric bilinear form. -/
def finiteFormQuadraticForm (L : FiniteFormCat K K) :
    QuadraticForm K L.obj.carrier :=
  LinearMap.BilinMap.toQuadraticMap L.obj.bilinMap

omit [LinearOrder K] in
/-- The quadratic form of an orthogonal sum is the product quadratic form. -/
@[simp]
theorem finiteFormQuadraticForm_orthogonalSum
    (L M : FiniteFormCat K K) :
    finiteFormQuadraticForm K (finiteFormOrthogonalSum L M) =
      (finiteFormQuadraticForm K L).prod (finiteFormQuadraticForm K M) := by
  ext x
  rfl

omit [LinearOrder K] in
/-- The quadratic form of an indexed orthogonal sum is the indexed sum. -/
@[simp]
theorem finiteFormQuadraticForm_indexedOrthogonalSum
    {I : Type} [Fintype I] (L : I → FiniteFormCat K K) :
    finiteFormQuadraticForm K (finiteFormIndexedOrthogonalSum L) =
      QuadraticMap.pi (fun i ↦ finiteFormQuadraticForm K (L i)) := by
  classical
  ext x
  simp only [finiteFormQuadraticForm,
    LinearMap.BilinMap.toQuadraticMap_apply,
    BilinModuleCat.bilinMap_apply]
  erw [QuadraticMap.pi_apply]
  simp only [LinearMap.BilinMap.toQuadraticMap_apply,
    BilinModuleCat.bilinMap_apply]
  exact finiteFormIndexedOrthogonalSum_pairing L x x

omit [LinearOrder K] in
/-- The quadratic form of an orthogonal power is the indexed sum of one form. -/
@[simp]
theorem finiteFormQuadraticForm_orthogonalPower
    (L : FiniteFormCat K K) (n : ℕ) :
    finiteFormQuadraticForm K (finiteFormOrthogonalPower L n) =
      QuadraticMap.pi (fun _ : Fin n ↦ finiteFormQuadraticForm K L) := by
  change finiteFormQuadraticForm K
      (finiteFormIndexedOrthogonalSum fun _ : Fin n ↦ L) = _
  exact finiteFormQuadraticForm_indexedOrthogonalSum K fun _ : Fin n ↦ L

/-- Currying identifies indexed copies of one diagonal quadratic form. -/
noncomputable def piWeightedSumSquaresIsometryEquiv
    {I J : Type} [Fintype I] [Fintype J] (w : J → K) :
    (QuadraticMap.pi fun _ : I ↦
      QuadraticMap.weightedSumSquares K w).IsometryEquiv
      (QuadraticMap.weightedSumSquares K
        (fun s : Σ _ : I, J ↦ w s.2)) where
  toLinearEquiv := (LinearEquiv.piCurry K fun _ _ ↦ K).symm
  map_app' x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      LinearEquiv.coe_coe, LinearEquiv.piCurry_symm_apply,
      QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
      QuadraticMap.pi_apply]
    exact Fintype.sum_sigma' fun i j ↦ w j * (x i j * x i j)

private def setOfSigmaEquivProd
    {I J : Type} {A : Type*} (f : J → A) (p : A → Prop) :
    {s : Σ _ : I, J // p (f s.2)} ≃ I × {j : J // p (f j)} where
  toFun s := ⟨s.1.1, ⟨s.1.2, s.2⟩⟩
  invFun s := ⟨⟨s.1, s.2.1⟩, s.2.2⟩
  left_inv s := by
    cases s with
    | mk s hs => cases s; rfl
  right_inv s := by
    cases s with
    | mk i s => cases s; rfl

private theorem ncard_setOf_sigma_const
    {I J : Type} {A : Type*} [Fintype I]
    (f : J → A) (p : A → Prop) :
    {s : Σ _ : I, J | p (f s.2)}.ncard =
      Fintype.card I * {j : J | p (f j)}.ncard := by
  calc
    {s : Σ _ : I, J | p (f s.2)}.ncard =
        Nat.card {s : Σ _ : I, J // p (f s.2)} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card (I × {j : J // p (f j)}) :=
      Nat.card_congr (setOfSigmaEquivProd f p)
    _ = Nat.card I * Nat.card {j : J // p (f j)} := Nat.card_prod _ _
    _ = Fintype.card I * {j : J | p (f j)}.ncard := by
      rw [Nat.card_eq_fintype_card]
      congr 1

/-- A weighted form on a sum type is the product of its two restrictions. -/
noncomputable def weightedSumSquaresSumIsometryEquiv
    {I J : Type*} [Fintype I] [Fintype J]
    (w₁ : I → K) (w₂ : J → K) :
    (QuadraticMap.weightedSumSquares K (Sum.elim w₁ w₂)).IsometryEquiv
      ((QuadraticMap.weightedSumSquares K w₁).prod
        (QuadraticMap.weightedSumSquares K w₂)) where
  toLinearEquiv := LinearEquiv.sumPiEquivProdPi K I J (fun _ ↦ K)
  map_app' x := by
    simp [QuadraticMap.weightedSumSquares_apply]

private theorem ncard_setOf_sum_elim
    {I J A : Type*} [Finite I] [Finite J]
    (f : I → A) (g : J → A) (p : A → Prop) :
    {s | p (Sum.elim f g s)}.ncard =
      {i | p (f i)}.ncard + {j | p (g j)}.ncard := by
  have hset : {s | p (Sum.elim f g s)} =
      Sum.inl '' {i | p (f i)} ∪ Sum.inr '' {j | p (g j)} := by
    ext s
    cases s <;> simp
  rw [hset, Set.ncard_union_eq Set.disjoint_image_inl_image_inr,
    Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]

/-- Positive, negative, and null ranks add under products of quadratic forms. -/
theorem quadraticSignature_prod [IsStrictOrderedRing K]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module K M₁] [Module K M₂]
    [Module.Finite K M₁] [Module.Finite K M₂]
    (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂) :
    (sigPos (Q₁.prod Q₂), sigNeg (Q₁.prod Q₂),
      Module.finrank K (Q₁.prod Q₂).radical) =
    (sigPos Q₁ + sigPos Q₂, sigNeg Q₁ + sigNeg Q₂,
      Module.finrank K Q₁.radical + Module.finrank K Q₂.radical) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by positivity)
  obtain ⟨w₁, hw₁⟩ := Q₁.equivalent_weightedSumSquares
  obtain ⟨w₂, hw₂⟩ := Q₂.equivalent_weightedSumSquares
  let hw : QuadraticMap.Equivalent (Q₁.prod Q₂)
      (QuadraticMap.weightedSumSquares K (Sum.elim w₁ w₂)) :=
    (hw₁.prod hw₂).trans
      ⟨(weightedSumSquaresSumIsometryEquiv K w₁ w₂).symm⟩
  apply Prod.ext
  · change sigPos (Q₁.prod Q₂) = sigPos Q₁ + sigPos Q₂
    rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares hw,
      QuadraticForm.sigPos_of_equiv_weightedSumSquares hw₁,
      QuadraticForm.sigPos_of_equiv_weightedSumSquares hw₂]
    exact ncard_setOf_sum_elim w₁ w₂ (0 < ·)
  · apply Prod.ext
    · change sigNeg (Q₁.prod Q₂) = sigNeg Q₁ + sigNeg Q₂
      rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw,
        QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw₁,
        QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw₂]
      exact ncard_setOf_sum_elim w₁ w₂ (· < 0)
    · change Module.finrank K (Q₁.prod Q₂).radical =
          Module.finrank K Q₁.radical + Module.finrank K Q₂.radical
      rw [QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hw,
        QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hw₁,
        QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hw₂]
      exact ncard_setOf_sum_elim w₁ w₂ (· = 0)

/-- An orthogonal power multiplies each part of a quadratic signature. -/
theorem quadraticSignature_pi_const [IsStrictOrderedRing K]
    {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (Q : QuadraticForm K M) (n : ℕ) :
    (sigPos (QuadraticMap.pi fun _ : Fin n ↦ Q),
      sigNeg (QuadraticMap.pi fun _ : Fin n ↦ Q),
      Module.finrank K (QuadraticMap.pi fun _ : Fin n ↦ Q).radical) =
    (n * sigPos Q, n * sigNeg Q,
      n * Module.finrank K Q.radical) := by
  letI : Invertible (2 : K) := invertibleOfNonzero (by positivity)
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares
  let hwPi : QuadraticMap.Equivalent
      (QuadraticMap.pi fun _ : Fin n ↦ Q)
      (QuadraticMap.pi fun _ : Fin n ↦
        QuadraticMap.weightedSumSquares K w) :=
    QuadraticMap.Equivalent.pi fun _ ↦ hw
  let hwTotal : QuadraticMap.Equivalent
      (QuadraticMap.pi fun _ : Fin n ↦ Q)
      (QuadraticMap.weightedSumSquares K
        (fun s : Σ _ : Fin n, Fin (Module.finrank K M) ↦ w s.2)) :=
    hwPi.trans ⟨piWeightedSumSquaresIsometryEquiv K w⟩
  apply Prod.ext
  · change sigPos (QuadraticMap.pi fun _ : Fin n ↦ Q) =
      n * sigPos Q
    rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares hwTotal,
      QuadraticForm.sigPos_of_equiv_weightedSumSquares hw]
    simpa using ncard_setOf_sigma_const (I := Fin n) w (0 < ·)
  · apply Prod.ext
    · change sigNeg (QuadraticMap.pi fun _ : Fin n ↦ Q) =
        n * sigNeg Q
      rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hwTotal,
        QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw]
      simpa using ncard_setOf_sigma_const (I := Fin n) w (· < 0)
    · change Module.finrank K
          (QuadraticMap.pi fun _ : Fin n ↦ Q).radical =
        n * Module.finrank K Q.radical
      rw [QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hwTotal,
        QuadraticForm.finrank_radical_of_equiv_weightedSumSquares hw]
      simpa using ncard_setOf_sigma_const (I := Fin n) w (· = 0)

/-- The underlying finite-dimensional module of a finite symmetric form. -/
def finiteFormForget : FiniteFormCat K K ⥤ ModuleCat K :=
  ObjectProperty.ι (isFiniteForm K K) ⋙
    LeanCategories.Modules.Bilinear.Valued.forget K K

/-- An isomorphism of finite symmetric forms gives an isometry of their quadratic forms. -/
def finiteFormQuadraticIsometryEquiv {L M : FiniteFormCat K K}
    (e : L ≅ M) :
    (finiteFormQuadraticForm K L).IsometryEquiv
      (finiteFormQuadraticForm K M) where
  __ := ((finiteFormForget K).mapIso e).toLinearEquiv
  map_app' x := BilinModuleCat.map_pairing e.hom.hom x x

/-- The total Sylvester signature `(positive, negative, nullity)`. -/
noncomputable def signature (L : FiniteFormCat K K) : ℕ × ℕ × ℕ :=
  let Q := finiteFormQuadraticForm K L
  (sigPos Q, sigNeg Q, Module.finrank K Q.radical)

/-- Signature is additive under orthogonal sums. -/
theorem signature_orthogonalSum [IsStrictOrderedRing K]
    (L M : FiniteFormCat K K) :
    signature K (finiteFormOrthogonalSum L M) =
      ((signature K L).1 + (signature K M).1,
        (signature K L).2.1 + (signature K M).2.1,
        (signature K L).2.2 + (signature K M).2.2) := by
  letI : Module.Finite K L.obj.carrier := L.property.1
  letI : Module.Finite K M.obj.carrier := M.property.1
  rw [signature, signature, signature,
    finiteFormQuadraticForm_orthogonalSum]
  exact quadraticSignature_prod K (finiteFormQuadraticForm K L)
    (finiteFormQuadraticForm K M)

/-- Signature is multiplied by the exponent under finite orthogonal powers. -/
theorem signature_orthogonalPower [IsStrictOrderedRing K]
    (L : FiniteFormCat K K) (n : ℕ) :
    signature K (finiteFormOrthogonalPower L n) =
      (n * (signature K L).1, n * (signature K L).2.1,
        n * (signature K L).2.2) := by
  letI : Module.Finite K L.obj.carrier := L.property.1
  rw [signature, signature, finiteFormQuadraticForm_orthogonalPower]
  exact quadraticSignature_pi_const K (finiteFormQuadraticForm K L) n

/-- The quadratic form represented by a matrix in the standard basis. -/
def matrixQuadraticForm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I K) : QuadraticForm K (I → K) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toBilin' A)

/-- The total signature of a symmetric matrix. -/
noncomputable def matrixSignature {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I K) : ℕ × ℕ × ℕ :=
  let Q := matrixQuadraticForm K A
  (sigPos Q, sigNeg Q, Module.finrank K Q.radical)

/-- The block matrix of an orthogonal sum. -/
noncomputable def matrixBlockSum
    {S : Type*} [Zero S]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix I I S) (B : Matrix J J S) :
    Matrix (I ⊕ J) (I ⊕ J) S :=
  Matrix.fromBlocks A 0 0 B

/-- The quadratic form of a block sum is the product quadratic form. -/
noncomputable def matrixBlockSumIsometry
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix I I K) (B : Matrix J J K) :
    (matrixQuadraticForm K (matrixBlockSum A B)).IsometryEquiv
      ((matrixQuadraticForm K A).prod (matrixQuadraticForm K B)) where
  toLinearEquiv := LinearEquiv.sumPiEquivProdPi K I J (fun _ ↦ K)
  map_app' x := by
    simp [matrixQuadraticForm, matrixBlockSum,
      Matrix.toBilin'_apply', dotProduct, Matrix.mulVec,
      Fintype.sum_sum_type, mul_add]

/-- Matrix signatures add under block sums. -/
theorem matrixSignature_blockSum [IsStrictOrderedRing K]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix I I K) (B : Matrix J J K) :
    matrixSignature K (matrixBlockSum A B) =
      ((matrixSignature K A).1 + (matrixSignature K B).1,
        (matrixSignature K A).2.1 + (matrixSignature K B).2.1,
        (matrixSignature K A).2.2 + (matrixSignature K B).2.2) := by
  let h : QuadraticMap.Equivalent
      (matrixQuadraticForm K (matrixBlockSum A B))
      ((matrixQuadraticForm K A).prod (matrixQuadraticForm K B)) :=
    ⟨matrixBlockSumIsometry K A B⟩
  simp only [matrixSignature]
  rw [h.sigPos_eq, h.sigNeg_eq, h.rank_radical_eq]
  exact quadraticSignature_prod K (matrixQuadraticForm K A)
    (matrixQuadraticForm K B)

/-- Ring maps preserve block sums. -/
theorem matrixBlockSum_map
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix I I R) (B : Matrix J J R) :
    (matrixBlockSum A B).map f =
      matrixBlockSum (A.map f) (B.map f) := by
  ext i j
  cases i <;> cases j <;> simp [matrixBlockSum]

/-- Negation swaps the positive and negative parts of a matrix signature. -/
@[simp]
theorem matrixSignature_neg {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I K) :
    matrixSignature K (-A) =
      ((matrixSignature K A).2.1, (matrixSignature K A).1,
        (matrixSignature K A).2.2) := by
  have hQ : matrixQuadraticForm K (-A) = -(matrixQuadraticForm K A) := by
    ext x
    simp [matrixQuadraticForm, Matrix.toBilin'_apply']
  have hRadical : (-(matrixQuadraticForm K A)).radical =
      (matrixQuadraticForm K A).radical := by
    ext x
    simp [QuadraticMap.mem_radical_iff']
  simp only [matrixSignature]
  rw [hQ, sigPos_neg, sigNeg_neg, hRadical]

/-- A basis identifies a finite formed module with its matrix quadratic form. -/
noncomputable def finiteFormQuadraticIsometryBasis
    {I : Type*} [Fintype I] [DecidableEq I]
    (L : FiniteFormCat K K) (b : Module.Basis I K L.obj.carrier) :
    (finiteFormQuadraticForm K L).IsometryEquiv
      (matrixQuadraticForm K (LinearMap.BilinForm.toMatrix b L.obj.bilinMap)) where
  toLinearEquiv := b.equivFun
  map_app' x := by
    change Matrix.toBilin' (LinearMap.BilinForm.toMatrix b L.obj.bilinMap)
      (b.equivFun x) (b.equivFun x) = L.obj.pairing x x
    rw [Matrix.toBilin'_apply', Module.Basis.equivFun_apply]
    exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
      b L.obj.bilinMap x x).symm

/-- A finite formed module has the signature of its Gram matrix. -/
theorem signature_eq_matrixSignature {I : Type*} [Fintype I] [DecidableEq I]
    (L : FiniteFormCat K K) (b : Module.Basis I K L.obj.carrier) :
    signature K L =
      matrixSignature K (LinearMap.BilinForm.toMatrix b L.obj.bilinMap) := by
  let h : QuadraticMap.Equivalent
      (finiteFormQuadraticForm K L)
      (matrixQuadraticForm K (LinearMap.BilinForm.toMatrix b L.obj.bilinMap)) :=
    ⟨finiteFormQuadraticIsometryBasis K L b⟩
  simp only [signature, matrixSignature]
  rw [h.sigPos_eq, h.sigNeg_eq, h.rank_radical_eq]

/-- A weighted diagonalization computes every part of a matrix signature. -/
theorem matrixSignature_eq_of_equivalent_weighted
    {I : Type*} [Fintype I] [DecidableEq I] [IsStrictOrderedRing K]
    (A : Matrix I I K) (w : I → K)
    (h : QuadraticMap.Equivalent (matrixQuadraticForm K A)
      (QuadraticMap.weightedSumSquares K w)) :
    matrixSignature K A =
      ({i | 0 < w i}.ncard, {i | w i < 0}.ncard, {i | w i = 0}.ncard) := by
  simp only [matrixSignature]
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares h,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares h,
    QuadraticForm.finrank_radical_of_equiv_weightedSumSquares h]

/-- An injective coordinate map gives a negative-definite Gram matrix. -/
theorem matrixSignature_neg_transpose_mul_self
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (B : Matrix I J ℝ) (hB : Function.Injective B.mulVec) :
    matrixSignature ℝ (-(B.transpose * B)) =
      (0, Fintype.card J, 0) := by
  let Q := matrixQuadraticForm ℝ (-(B.transpose * B))
  have hneg : (-Q).PosDef := by
    intro x hx
    have hBx : B.mulVec x ≠ 0 := by
      intro h
      exact hx (hB (h.trans (Matrix.mulVec_zero B).symm))
    have hsquares : 0 < dotProduct (B.mulVec x) (B.mulVec x) :=
      lt_of_le_of_ne (Fintype.sum_nonneg fun _ ↦ mul_self_nonneg _)
        (Ne.symm (dotProduct_self_eq_zero.not.mpr hBx))
    simp only [QuadraticMap.neg_apply, Left.neg_pos_iff, gt_iff_lt]
    change Matrix.toBilin' (-(B.transpose * B)) x x < 0
    rw [Matrix.toBilin'_apply', Matrix.neg_mulVec, dotProduct_neg,
      neg_lt_zero]
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
    exact hsquares
  have hsigNeg : sigNeg Q = Fintype.card J := by
    apply le_antisymm
    · simpa [Q, Module.finrank_fintype_fun_eq_card] using
        sigPos_le_finrank (-Q)
    · have htop : ((-Q).restrict (⊤ : Submodule ℝ (J → ℝ))).PosDef := by
        intro x hx
        exact hneg x.1 (by simpa using hx)
      simpa [Module.finrank_fintype_fun_eq_card] using
        le_sigNeg_of_negDef Q htop
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hsigNeg, Module.finrank_fintype_fun_eq_card] at hsum
  have hsigPos : sigPos Q = 0 := by omega
  have hradical : Module.finrank ℝ Q.radical = 0 := by omega
  change (sigPos Q, sigNeg Q, Module.finrank ℝ Q.radical) = _
  rw [hsigPos, hsigNeg, hradical]

/-- Signature is invariant under isomorphisms of finite symmetric forms. -/
theorem signature_eq_of_iso {L M : FiniteFormCat K K} (e : L ≅ M) :
    signature K L = signature K M := by
  let h : QuadraticMap.Equivalent
      (finiteFormQuadraticForm K L) (finiteFormQuadraticForm K M) :=
    ⟨finiteFormQuadraticIsometryEquiv K e⟩
  simp only [signature]
  rw [h.sigPos_eq, h.sigNeg_eq, h.rank_radical_eq]

/-- Positive, negative, and null ranks sum to the carrier rank. -/
theorem signature_sum [IsStrictOrderedRing K] (L : FiniteFormCat K K) :
    (signature K L).1 + (signature K L).2.1 + (signature K L).2.2 =
      Module.finrank K L.obj.carrier := by
  letI : Module.Finite K L.obj.carrier := L.property.1
  exact QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := finiteFormQuadraticForm K L)

/-- Total signature as a functor on the isomorphism core. -/
noncomputable def signatureFunctor :
    Core (FiniteFormCat K K) ⥤ Discrete (ℕ × ℕ × ℕ) where
  obj L := Discrete.mk (signature K L.of)
  map f := Discrete.eqToHom (signature_eq_of_iso K f.iso)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The real signature of a finite projective integral lattice. -/
noncomputable def integralSignature
    (L : FiniteProjectiveLatticeCat ℤ ℤ) : ℕ × ℕ × ℕ :=
  signature ℝ
    ((finiteProjectiveToFiniteForm ℝ ℝ).obj
      ((baseChangeFiniteIntegral ℤ ℝ).obj L))

/-- An integral lattice has the signature of its real Gram matrix. -/
theorem integralSignature_eq_matrixSignature {I : Type*} [Fintype I]
    [DecidableEq I] (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis I ℤ L.obj.obj.carrier) :
    integralSignature L = matrixSignature ℝ
      ((gramMatrix L.obj b).map (Int.castRingHom ℝ)) := by
  let M := (finiteProjectiveToFiniteForm ℝ ℝ).obj
    ((baseChangeFiniteIntegral ℤ ℝ).obj L)
  let bℝ : Module.Basis I ℝ M.obj.carrier := b.baseChange ℝ
  have hMatrix : LinearMap.BilinForm.toMatrix bℝ M.obj.bilinMap =
      (gramMatrix L.obj b).map (Int.castRingHom ℝ) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    have hb (k : I) : bℝ k = (1 ⊗ₜ[ℤ] b k) := by
      dsimp [bℝ]
      exact b.baseChange_apply ℝ k
    rw [hb i, hb j]
    dsimp [M]
    change ((baseChangeIntegral ℤ ℝ).obj L.obj).obj.pairing
      (1 ⊗ₜ[ℤ] b i) (1 ⊗ₜ[ℤ] b j) = _
    rw [baseChangeIntegral_pairing_tmul]
    simp [gramMatrix, LinearMap.BilinForm.toMatrix_apply]
  rw [integralSignature]
  rw [signature_eq_matrixSignature ℝ M bℝ]
  exact congrArg (matrixSignature ℝ) hMatrix

/-- The product basis gives the block Gram matrix of an orthogonal sum. -/
theorem gramMatrix_finiteProjectiveOrthogonalSum
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (L M : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis I ℤ L.obj.obj.carrier)
    (c : Module.Basis J ℤ M.obj.obj.carrier) :
    gramMatrix (finiteProjectiveOrthogonalSum L M).obj (b.prod c) =
      matrixBlockSum (gramMatrix L.obj b) (gramMatrix M.obj c) := by
  ext i j
  rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply]
  change L.obj.obj.pairing ((b.prod c i).1) ((b.prod c j).1) +
      M.obj.obj.pairing ((b.prod c i).2) ((b.prod c j).2) = _
  cases i <;> cases j <;>
    simp [matrixBlockSum, gramMatrix,
      LinearMap.BilinForm.toMatrix_apply]

/-- Integral signatures add under finite projective orthogonal sums. -/
theorem integralSignature_orthogonalSum
    (L M : FiniteProjectiveLatticeCat ℤ ℤ) :
    integralSignature (finiteProjectiveOrthogonalSum L M) =
      ((integralSignature L).1 + (integralSignature M).1,
        (integralSignature L).2.1 + (integralSignature M).2.1,
        (integralSignature L).2.2 + (integralSignature M).2.2) := by
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  letI : Module.Free ℤ M.obj.obj.carrier := M.carrier_free
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  letI : Module.Finite ℤ M.obj.obj.carrier := M.property
  let b := Module.Free.chooseBasis ℤ L.obj.obj.carrier
  let c := Module.Free.chooseBasis ℤ M.obj.obj.carrier
  rw [integralSignature_eq_matrixSignature
    (finiteProjectiveOrthogonalSum L M) (b.prod c)]
  rw [gramMatrix_finiteProjectiveOrthogonalSum L M b c,
    matrixBlockSum_map]
  rw [matrixSignature_blockSum]
  rw [← integralSignature_eq_matrixSignature L b,
    ← integralSignature_eq_matrixSignature M c]

/-- Negation swaps the positive and negative parts of an integral signature. -/
@[simp]
theorem integralSignature_opposite (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    integralSignature (oppositeFiniteProjectiveLattice L) =
      ((integralSignature L).2.1, (integralSignature L).1,
        (integralSignature L).2.2) := by
  classical
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  let b := Module.Free.chooseBasis ℤ L.obj.obj.carrier
  rw [integralSignature_eq_matrixSignature
    (oppositeFiniteProjectiveLattice L) b]
  rw [integralSignature_eq_matrixSignature L b]
  change matrixSignature ℝ
    ((gramMatrix (oppositeLattice L.obj) b).map (Int.castRingHom ℝ)) = _
  rw [gramMatrix_opposite]
  rw [Matrix.map_neg _ (map_neg (Int.castRingHom ℝ))]
  exact matrixSignature_neg ℝ _

/-- Real signature as a functor on finite integral lattices and their isomorphisms. -/
noncomputable def integralSignatureFunctor :
    Core (FiniteProjectiveLatticeCat ℤ ℤ) ⥤ Discrete (ℕ × ℕ × ℕ) :=
  (baseChangeFiniteIntegral ℤ ℝ).core ⋙
    (finiteProjectiveToFiniteForm ℝ ℝ).core ⋙
      signatureFunctor ℝ

/-- A signature value is positive definite when it has no negative or null part. -/
def IsPositiveDefiniteSignature : ℕ × ℕ × ℕ → Prop
  | (_, n, z) => n = 0 ∧ z = 0

/-- A signature value is negative definite when it has no positive or null part. -/
def IsNegativeDefiniteSignature : ℕ × ℕ × ℕ → Prop
  | (p, _, z) => p = 0 ∧ z = 0

/-- A signature value is positive semidefinite when it has no negative part. -/
def IsPositiveSemidefiniteSignature : ℕ × ℕ × ℕ → Prop
  | (_, n, _) => n = 0

/-- A signature value is negative semidefinite when it has no positive part. -/
def IsNegativeSemidefiniteSignature : ℕ × ℕ × ℕ → Prop
  | (p, _, _) => p = 0

/-- A signature value is indefinite when both signed parts are nonzero. -/
def IsIndefiniteSignature : ℕ × ℕ × ℕ → Prop
  | (p, n, _) => 0 < p ∧ 0 < n

/-- A nondegenerate signature is Lorentzian when its smaller signed rank is one. -/
def IsLorentzianSignature : ℕ × ℕ × ℕ → Prop
  | (p, n, z) => min p n = 1 ∧ z = 0

/-- A finite integral lattice is positive definite through its real signature. -/
def IsPositiveDefiniteLattice (L : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  IsPositiveDefiniteSignature (integralSignature L)

/-- A finite integral lattice is negative definite through its real signature. -/
def IsNegativeDefiniteLattice (L : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  IsNegativeDefiniteSignature (integralSignature L)

/-- A finite integral lattice is positive semidefinite through its real signature. -/
def IsPositiveSemidefiniteLattice
    (L : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  IsPositiveSemidefiniteSignature (integralSignature L)

/-- A finite integral lattice is negative semidefinite through its real signature. -/
def IsNegativeSemidefiniteLattice
    (L : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  IsNegativeSemidefiniteSignature (integralSignature L)

/-- A finite integral lattice is indefinite through its real signature. -/
def IsIndefiniteLattice (L : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  IsIndefiniteSignature (integralSignature L)

/-- A finite integral lattice is Lorentzian through its real signature. -/
def IsLorentzianLattice (L : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  IsLorentzianSignature (integralSignature L)

end LeanCategories.Lattices.Valued
