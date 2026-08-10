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
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
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

/-- The quadratic form represented by a matrix in the standard basis. -/
def matrixQuadraticForm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I K) : QuadraticForm K (I → K) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toBilin' A)

/-- The total signature of a symmetric matrix. -/
noncomputable def matrixSignature {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I K) : ℕ × ℕ × ℕ :=
  let Q := matrixQuadraticForm K A
  (sigPos Q, sigNeg Q, Module.finrank K Q.radical)

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
