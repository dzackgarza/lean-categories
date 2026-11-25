/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Data.Matrix.Block
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Extension.Linear
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Block-triangular general-linear groups

For a map `b : ι → κ` assigning basis indices to blocks, this file identifies the split extension
of the block-triangular group by its product of diagonal general-linear groups. The normal factor
is the block-unipotent kernel. The semidirect-product equivalence sends `(u, d)` to `u * section d`,
so both the conjugation action and the factor order are explicit.

The elementary-generation theorem and the transport to stabilizers of adapted flags are proved in
this module and `LeanCategories.Modules.Flags`, respectively. No form-preservation condition is
imposed: this is general-linear, not orthogonal, group theory.
-/

@[expose] public section

open scoped Matrix

namespace LeanCategories.Modules

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [LinearOrder κ] [CommRing R]

/-- The indices belonging to one block. -/
abbrev BlockIndex (b : ι → κ) (k : κ) := {i // b i = k}

/-- The subgroup of invertible matrices which are upper block-triangular for `b`. -/
def blockTriangularSubgroup (b : ι → κ) : Subgroup (Matrix.GeneralLinearGroup ι R) where
  carrier := {A | Matrix.BlockTriangular (A : Matrix ι ι R) b}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' hA hB := hA.mul hB
  inv_mem' {A} hA := by
    change Matrix.BlockTriangular (↑A⁻¹ : Matrix ι ι R) b
    letI : Invertible (A : Matrix ι ι R) := A.invertible
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hA

@[simp] theorem mem_blockTriangularSubgroup {b : ι → κ}
    {A : Matrix.GeneralLinearGroup ι R} :
    A ∈ blockTriangularSubgroup b ↔ Matrix.BlockTriangular (A : Matrix ι ι R) b :=
  Iff.rfl

/-- An inverse of a block-triangular unit is again block-triangular. -/
theorem blockTriangular_inv {b : ι → κ} {A : Matrix.GeneralLinearGroup ι R}
    (hA : Matrix.BlockTriangular (A : Matrix ι ι R) b) :
    Matrix.BlockTriangular (↑A⁻¹ : Matrix ι ι R) b := by
  letI : Invertible (A : Matrix ι ι R) := A.invertible
  simpa only [Matrix.GeneralLinearGroup.coe_inv] using
    Matrix.blockTriangular_inv_of_blockTriangular hA

/-- Multiplication restricts to each diagonal block of two block-triangular matrices. -/
theorem toSquareBlock_mul_of_blockTriangular {b : ι → κ} {A B : Matrix ι ι R}
    (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (k : κ) :
    (A * B).toSquareBlock b k = A.toSquareBlock b k * B.toSquareBlock b k := by
  let p : ι → Prop := fun i => b i = k
  change (A * B).toBlock p p = A.toBlock p p * B.toBlock p p
  rw [Matrix.toBlock_mul_eq_add p p p]
  have hz : A.toBlock p (fun i => ¬p i) * B.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_trichotomy (b (l : ι)) k with hl | hl | hl
    · have hzero : A (i : ι) (l : ι) = 0 := hA (by rw [i.property]; exact hl)
      simp [hzero]
    · exact (l.property hl).elim
    · have hzero : B (l : ι) (j : ι) = 0 := hB (by rw [j.property]; exact hl)
      simp [hzero]
  rw [hz, add_zero]

@[simp] theorem toSquareBlock_one (b : ι → κ) (k : κ) :
    (1 : Matrix ι ι R).toSquareBlock b k = 1 :=
  Matrix.toBlock_one_self _

/-- The diagonal-block unit determined by an element of the block-triangular group. -/
def diagonalUnit (b : ι → κ) (A : blockTriangularSubgroup (R := R) b) (k : κ) :
    Matrix.GeneralLinearGroup (BlockIndex b k) R where
  val := (A.1.1 : Matrix ι ι R).toSquareBlock b k
  inv := (↑A.1⁻¹ : Matrix ι ι R).toSquareBlock b k
  val_inv := by
    rw [← toSquareBlock_mul_of_blockTriangular A.2 (blockTriangular_inv A.2)]
    change ((((A.1 : Matrix.GeneralLinearGroup ι R) * A.1⁻¹ :
      Matrix.GeneralLinearGroup ι R)) : Matrix ι ι R).toSquareBlock b k = 1
    rw [mul_inv_cancel]
    exact toSquareBlock_one b k
  inv_val := by
    rw [← toSquareBlock_mul_of_blockTriangular (blockTriangular_inv A.2) A.2]
    change (((A.1⁻¹ * A.1 : Matrix.GeneralLinearGroup ι R)) :
      Matrix ι ι R).toSquareBlock b k = 1
    rw [inv_mul_cancel]
    exact toSquareBlock_one b k

/-- Projection from a block-triangular group to the product of its diagonal general-linear
parts. -/
def diagonalHom (b : ι → κ) :
    blockTriangularSubgroup (R := R) b →* ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R :=
  MonoidHom.pi fun k =>
    { toFun := fun A => diagonalUnit b A k
      map_one' := by
        apply Units.ext
        change (1 : Matrix ι ι R).toSquareBlock b k = 1
        exact toSquareBlock_one b k
      map_mul' := fun A B => Matrix.GeneralLinearGroup.ext fun _ _ =>
        congr_fun₂ (toSquareBlock_mul_of_blockTriangular A.2 B.2 k) _ _ }

/-- The block-unipotent kernel of the diagonal projection. -/
def blockUnipotentSubgroup (b : ι → κ) := (diagonalHom (R := R) b).ker

/-- Reindexing and block-diagonal insertion give the diagonal section into the full general-linear
group. -/
def blockDiagonalGL (b : ι → κ) :
    (∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) →* Matrix.GeneralLinearGroup ι R :=
  (Units.mapEquiv (Matrix.reindexAlgEquiv R R (Equiv.sigmaFiberEquiv b)).toMulEquiv).toMonoidHom.comp
    ((Units.map (Matrix.blockDiagonal'RingHom (BlockIndex b) R).toMonoidHom).comp
      MulEquiv.piUnits.symm.toMonoidHom)

@[simp] theorem blockDiagonalGL_val_apply {b : ι → κ}
    (D : ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) (i j : ι) :
    ((blockDiagonalGL b D : Matrix.GeneralLinearGroup ι R) : Matrix ι ι R) i j =
      Matrix.blockDiagonal' (fun k => (D k : Matrix (BlockIndex b k) (BlockIndex b k) R))
        ⟨b i, i, rfl⟩ ⟨b j, j, rfl⟩ :=
  rfl

/-- The diagonal section is block-triangular. -/
theorem blockDiagonalGL_blockTriangular {b : ι → κ}
    (D : ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) :
    Matrix.BlockTriangular ((blockDiagonalGL b D : Matrix.GeneralLinearGroup ι R) :
      Matrix ι ι R) b := by
  rw [show ((blockDiagonalGL b D : Matrix.GeneralLinearGroup ι R) : Matrix ι ι R) =
    Matrix.reindexAlgEquiv R R (Equiv.sigmaFiberEquiv b)
      (Matrix.blockDiagonal' fun k => (D k : Matrix (BlockIndex b k) (BlockIndex b k) R)) from rfl]
  rw [Matrix.coe_reindexAlgEquiv, Matrix.blockTriangular_reindex_iff]
  have hb : b ∘ (Equiv.sigmaFiberEquiv b) = Sigma.fst := by
    funext x
    rcases x with ⟨k, i, hi⟩
    simpa only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply] using hi
  rw [hb]
  exact Matrix.blockTriangular_blockDiagonal'
    (R := R) (fun k => (D k : Matrix (BlockIndex b k) (BlockIndex b k) R))

/-- The block-diagonal splitting, valued in the block-triangular group. -/
def blockDiagonalSection (b : ι → κ) :
    (∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) →*
      blockTriangularSubgroup (R := R) b where
  toFun D := ⟨blockDiagonalGL b D, blockDiagonalGL_blockTriangular D⟩
  map_one' := Subtype.ext (blockDiagonalGL b).map_one
  map_mul' D E := Subtype.ext ((blockDiagonalGL b).map_mul D E)

@[simp] theorem diagonalHom_blockDiagonalSection {b : ι → κ}
    (D : ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) :
    diagonalHom b (blockDiagonalSection b D) = D := by
  funext k
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((blockDiagonalGL b D : Matrix.GeneralLinearGroup ι R) : Matrix ι ι R)
    (i : ι) (j : ι) = (D k : Matrix (BlockIndex b k) (BlockIndex b k) R) i j
  rw [blockDiagonalGL_val_apply]
  have hi : (⟨b (i : ι), (i : ι), rfl⟩ : Σ k, BlockIndex b k) = ⟨k, i⟩ := by
    rcases i with ⟨i, rfl⟩
    rfl
  have hj : (⟨b (j : ι), (j : ι), rfl⟩ : Σ k, BlockIndex b k) = ⟨k, j⟩ := by
    rcases j with ⟨j, rfl⟩
    rfl
  rw [hi, hj]
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _

/-- The short exact sequence from the block-unipotent group to the diagonal graded pieces. -/
def blockDiagonalGroupExtension (b : ι → κ) :
    GroupExtension (blockUnipotentSubgroup (R := R) b) (blockTriangularSubgroup (R := R) b)
      (∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) where
  inl := (blockUnipotentSubgroup (R := R) b).subtype
  rightHom := diagonalHom b
  inl_injective := Subtype.coe_injective
  range_inl_eq_ker_rightHom := (blockUnipotentSubgroup b).range_subtype
  rightHom_surjective D := ⟨blockDiagonalSection b D, diagonalHom_blockDiagonalSection D⟩

/-- The displayed diagonal splitting of the block-triangular group extension. -/
def blockDiagonalSplitting (b : ι → κ) :
    (blockDiagonalGroupExtension (R := R) b).Splitting where
  toMonoidHom := blockDiagonalSection b
  rightInverse_rightHom := diagonalHom_blockDiagonalSection (R := R)

/-- The block-triangular group is the semidirect product of its unipotent kernel and the product of
its diagonal general-linear groups. The action is conjugation by the diagonal section. -/
noncomputable def blockTriangularSemidirectEquiv (b : ι → κ) :
    blockUnipotentSubgroup (R := R) b ⋊[(blockDiagonalSplitting b).conjAct]
      (∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) ≃*
        blockTriangularSubgroup (R := R) b :=
  (blockDiagonalSplitting b).semidirectProductMulEquiv

/-- In the semidirect-product identification, the pair `(u, d)` maps to `u` followed by the diagonal
section `d`; in particular, the unipotent factor is on the left. -/
@[simp] theorem blockTriangularSemidirectEquiv_apply (b : ι → κ)
    (u : blockUnipotentSubgroup (R := R) b)
    (D : ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) :
    blockTriangularSemidirectEquiv b ⟨u, D⟩ = u.1 * blockDiagonalSection b D :=
  rfl

section UnitriangularGeneration

variable {η : Type u} [Fintype η] [DecidableEq η] [LinearOrder η]

/-- An upper-triangular matrix with diagonal entries equal to one. -/
def UpperUnitriangular (A : Matrix η η R) : Prop :=
  A.BlockTriangular id ∧ ∀ i, A i i = 1

/-- The upper elementary matrix `1 + a E_{ij}`, for `i < j`. -/
def upperTransvection {i j : η} (hij : i < j) (a : R) : Matrix.GeneralLinearGroup η R :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij.ne a)

@[simp] theorem upperTransvection_coe {i j : η} (hij : i < j) (a : R) :
    ((upperTransvection hij a : Matrix.GeneralLinearGroup η R) : Matrix η η R) =
      Matrix.transvection i j a :=
  rfl

/-- The set of permitted elementary generators. -/
def upperTransvectionSet : Set (Matrix.GeneralLinearGroup η R) :=
  {g | ∃ (i j : η) (hij : i < j) (a : R), g = upperTransvection hij a}

/-- The subgroup generated by all upper elementary matrices. -/
def upperTransvectionSubgroup : Subgroup (Matrix.GeneralLinearGroup η R) :=
  Subgroup.closure (upperTransvectionSet (R := R) (η := η))

@[simp] theorem upperUnitriangular_one :
    UpperUnitriangular (1 : Matrix η η R) :=
  ⟨Matrix.blockTriangular_one, by simp⟩

theorem upperUnitriangular_transvection {i j : η} (hij : i < j) (a : R) :
    UpperUnitriangular (Matrix.transvection i j a) := by
  refine ⟨Matrix.blockTriangular_transvection (b := id) (by simpa using hij.le) a, ?_⟩
  intro k
  by_cases h : i = k ∧ j = k
  · rcases h with ⟨rfl, rfl⟩
    exact (hij.false).elim
  · simp [Matrix.transvection, Matrix.single, h]

theorem upperUnitriangular_mul {A B : Matrix η η R}
    (hA : UpperUnitriangular A) (hB : UpperUnitriangular B) :
    UpperUnitriangular (A * B) := by
  refine ⟨hA.1.mul hB.1, fun i => ?_⟩
  classical
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp [hA.2, hB.2]
  · intro j _ hji
    by_cases h : j < i
    · rw [hA.1 (by simpa using h), zero_mul]
    · rw [hB.1 (by simpa using lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hji)), mul_zero]
  · simp

theorem upperTransvection_upperUnitriangular {i j : η} (hij : i < j) (a : R) :
    UpperUnitriangular ((upperTransvection hij a : Matrix.GeneralLinearGroup η R) :
      Matrix η η R) :=
  upperUnitriangular_transvection hij a

theorem upperTransvection_mem {i j : η} (hij : i < j) (a : R) :
    upperTransvection hij a ∈ upperTransvectionSubgroup (R := R) (η := η) :=
  Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩

/-- One can clear a finite set of columns of a prescribed row, without changing any row which was
already the corresponding identity row. All factors used are upper elementary matrices. -/
theorem exists_rowClearing (A : Matrix η η R) (hA : UpperUnitriangular A)
    (a : η) (P s : Finset η) (haP : a ∉ P) (hs : ∀ j ∈ s, a < j)
    (hP : ∀ i ∈ P, ∀ j, A i j = (1 : Matrix η η R) i j) :
    ∃ T : Matrix.GeneralLinearGroup η R,
      T ∈ upperTransvectionSubgroup (R := R) (η := η) ∧
      UpperUnitriangular (T : Matrix η η R) ∧
      (∀ i ∈ P, ∀ j, ((A * (T : Matrix η η R)) i j) = (1 : Matrix η η R) i j) ∧
      (∀ j, (A * (T : Matrix η η R)) a j = if j ∈ s then 0 else A a j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, Subgroup.one_mem _, upperUnitriangular_one, ?_, ?_⟩
      · simpa only [Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one] using hP
      · simp
  | @insert j s hj ih =>
      have haj : a < j := hs j (Finset.mem_insert_self _ _)
      have hs' : ∀ q ∈ s, a < q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      obtain ⟨T, hT, hTu, hP', hrow⟩ := ih hs'
      let E := upperTransvection haj (-A a j)
      have hE : E ∈ upperTransvectionSubgroup (R := R) (η := η) := upperTransvection_mem haj _
      have hEu : UpperUnitriangular (E : Matrix η η R) := upperTransvection_upperUnitriangular haj _
      have hTj : (A * (T : Matrix η η R)) a j = A a j := by
        rw [hrow, if_neg hj]
      have hTa : (A * (T : Matrix η η R)) a a = 1 := by
        rw [hrow]
        have ha : a ∉ s := fun h => (hs a (Finset.mem_insert_of_mem h)).false
        simp [ha, hA.2]
      refine ⟨T * E, mul_mem hT hE, upperUnitriangular_mul hTu hEu, ?_, ?_⟩
      · intro i hi q
        simp only [E, Matrix.GeneralLinearGroup.coe_mul, upperTransvection_coe,
          ← Matrix.mul_assoc]
        have hia : i ≠ a := fun h => haP (h ▸ hi)
        have hid : (A * (T : Matrix η η R)) i a = 0 := by
          rw [hP' i hi, Matrix.one_apply, if_neg hia]
        by_cases hq : q = j
        · subst q
          change (A * (T : Matrix η η R) * Matrix.transvection a j (-A a j)) i j = _
          rw [Matrix.mul_transvection_apply_same, hP' i hi, hid]
          simp
        · change (A * (T : Matrix η η R) * Matrix.transvection a j (-A a j)) i q = _
          rw [Matrix.mul_transvection_apply_of_ne a j i q hq]
          exact hP' i hi q
      · intro q
        simp only [E, Matrix.GeneralLinearGroup.coe_mul, upperTransvection_coe,
          ← Matrix.mul_assoc]
        by_cases hq : q = j
        · subst q
          change (A * (T : Matrix η η R) * Matrix.transvection a j (-A a j)) a j = _
          rw [Matrix.mul_transvection_apply_same, hTj, hTa]
          simp
        · change (A * (T : Matrix η η R) * Matrix.transvection a j (-A a j)) a q = _
          rw [Matrix.mul_transvection_apply_of_ne a j a q hq, hrow]
          by_cases hqs : q ∈ s <;> simp [hqs, hq]

/-- Clear one prescribed row while preserving a finite set of identity rows. -/
theorem exists_clearRow (A : Matrix η η R) (hA : UpperUnitriangular A)
    (a : η) (P : Finset η) (haP : a ∉ P)
    (hP : ∀ i ∈ P, ∀ j, A i j = (1 : Matrix η η R) i j) :
    ∃ T : Matrix.GeneralLinearGroup η R,
      T ∈ upperTransvectionSubgroup (R := R) (η := η) ∧
      UpperUnitriangular (T : Matrix η η R) ∧
      (∀ i ∈ insert a P, ∀ j,
        (A * (T : Matrix η η R)) i j = (1 : Matrix η η R) i j) := by
  classical
  let s := Finset.univ.filter fun j => a < j
  obtain ⟨T, hT, hTu, hP', hrow⟩ :=
    exists_rowClearing A hA a P s haP (fun _ h => (Finset.mem_filter.mp h).2) hP
  refine ⟨T, hT, hTu, fun i hi q => ?_⟩
  rcases Finset.mem_insert.mp hi with hia | hi
  · subst i
    rw [hrow]
    by_cases haq : a < q
    · have hmem : q ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, haq⟩
      simp [hmem, Matrix.one_apply, ne_of_lt haq]
    · have hnot : q ∉ s := fun h => haq (Finset.mem_filter.mp h).2
      rw [if_neg hnot]
      by_cases hqa : q = a
      · subst q
        simp [hA.2]
      · have hqa' : q < a := lt_of_le_of_ne (le_of_not_gt haq) hqa
        rw [hA.1 (by simpa using hqa'), Matrix.one_apply, if_neg (Ne.symm hqa)]
  · exact hP' i hi q

/-- Right multiplication by upper elementary matrices reduces every upper-unitriangular matrix to
the identity. -/
theorem exists_upperTransvection_reduction (A : Matrix η η R) (hA : UpperUnitriangular A) :
    ∃ T : Matrix.GeneralLinearGroup η R,
      T ∈ upperTransvectionSubgroup (R := R) (η := η) ∧
      UpperUnitriangular (T : Matrix η η R) ∧
      A * (T : Matrix η η R) = 1 := by
  classical
  have hrows : ∀ s : Finset η, ∃ T : Matrix.GeneralLinearGroup η R,
      T ∈ upperTransvectionSubgroup (R := R) (η := η) ∧
      UpperUnitriangular (T : Matrix η η R) ∧
      (∀ i ∈ s, ∀ j, (A * (T : Matrix η η R)) i j = (1 : Matrix η η R) i j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨1, Subgroup.one_mem _, upperUnitriangular_one, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨T, hT, hTu, hP⟩ := ih
        have hAT : UpperUnitriangular (A * (T : Matrix η η R)) :=
          upperUnitriangular_mul hA hTu
        obtain ⟨E, hE, hEu, hclear⟩ := exists_clearRow
          (A * (T : Matrix η η R)) hAT a s ha hP
        refine ⟨T * E, mul_mem hT hE, upperUnitriangular_mul hTu hEu, ?_⟩
        simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_assoc] using hclear
  obtain ⟨T, hT, hTu, hclear⟩ := hrows Finset.univ
  exact ⟨T, hT, hTu, Matrix.ext fun i j => hclear i (Finset.mem_univ i) j⟩

/-- The elementary matrices generate the upper-unitriangular group. -/
theorem upperUnitriangular_mem_upperTransvectionSubgroup
    {A : Matrix.GeneralLinearGroup η R} (hA : UpperUnitriangular (A : Matrix η η R)) :
    A ∈ upperTransvectionSubgroup (R := R) (η := η) := by
  obtain ⟨T, hT, -, hAT⟩ := exists_upperTransvection_reduction (A : Matrix η η R) hA
  have hA_T : A * T = 1 := Units.ext hAT
  have hAT' : A = T⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact hA_T
  rw [hAT']
  exact Subgroup.inv_mem _ hT

end UnitriangularGeneration

section BlockGeneration

/-- The partial order which compares distinct blocks and leaves different indices in one block
incomparable. -/
def BlockOrder (b : ι → κ) := ι

instance (b : ι → κ) : PartialOrder (BlockOrder b) where
  le i j := b i < b j ∨ i = j
  le_refl _ := Or.inr rfl
  le_trans i j k hij hjk := by
    rcases hij with hij | rfl
    · rcases hjk with hjk | rfl
      · exact Or.inl (hij.trans hjk)
      · exact Or.inl hij
    · exact hjk
  le_antisymm i j hij hji := by
    rcases hij with hij | rfl
    · rcases hji with hji | rfl
      · exact (hij.trans hji).false.elim
      · rfl
    · rfl

instance (b : ι → κ) : Fintype (BlockOrder b) := inferInstanceAs (Fintype ι)
instance (b : ι → κ) : DecidableEq (BlockOrder b) := inferInstanceAs (DecidableEq ι)

/-- A linear extension of the strict-block order. -/
abbrev BlockLinearOrder (b : ι → κ) := LinearExtension (BlockOrder b)

instance (b : ι → κ) : Fintype (BlockLinearOrder b) :=
  inferInstanceAs (Fintype (BlockOrder b))
instance (b : ι → κ) : DecidableEq (BlockLinearOrder b) :=
  inferInstanceAs (DecidableEq (BlockOrder b))

/-- The underlying-type equivalence between the linear extension and the original index type. -/
def blockOrderEquiv (b : ι → κ) : BlockLinearOrder b ≃ ι := Equiv.refl _

/-- Reindex a general-linear element into the chosen linear extension of the block order. -/
def blockOrderGL (b : ι → κ) : Matrix.GeneralLinearGroup ι R ≃*
    Matrix.GeneralLinearGroup (BlockLinearOrder b) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (blockOrderEquiv b).symm).toMulEquiv

@[simp] theorem blockOrderGL_apply (b : ι → κ) (A : Matrix.GeneralLinearGroup ι R)
    (i j : BlockLinearOrder b) :
    ((blockOrderGL b A : Matrix.GeneralLinearGroup (BlockLinearOrder b) R) :
      Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) i j = (A : Matrix ι ι R) i j :=
  rfl

/-- Strict block inequalities agree with the order on `BlockOrder`, hence hold in its linear
extension. -/
theorem block_le_of_block_lt {b : ι → κ} {i j : BlockLinearOrder b} (hij : b i < b j) :
    i ≤ j :=
  (toLinearExtension : BlockOrder b →o BlockLinearOrder b).monotone (Or.inl hij)

/-- Distinct block indices cannot be reversed by the linear extension. -/
theorem block_lt_of_lt_of_ne {b : ι → κ} {i j : BlockLinearOrder b}
    (hij : i < j) (hne : b i ≠ b j) : b i < b j := by
  rcases lt_trichotomy (b i) (b j) with h | h | h
  · exact h
  · exact (hne h).elim
  · exact ((not_le_of_gt hij) (block_le_of_block_lt h)).elim

/-- Identity on each diagonal block, with no condition away from the diagonal blocks. -/
def BlockDiagonalUnitary (A : Matrix ι ι R) (b : ι → κ) : Prop :=
  ∀ i j, b i = b j → A i j = (1 : Matrix ι ι R) i j

@[simp] theorem blockDiagonalUnitary_one (b : ι → κ) :
    BlockDiagonalUnitary (1 : Matrix ι ι R) b := fun _ _ _ => rfl

@[simp] theorem one_blockIndex_apply (b : ι → κ) (k : κ) (i j : BlockIndex b k) :
    (1 : Matrix (BlockIndex b k) (BlockIndex b k) R) i j =
      (1 : Matrix ι ι R) (i : ι) (j : ι) := by
  by_cases h : i = j
  · subst j
    simp
  · have h' : (i : ι) ≠ (j : ι) := fun e => h (Subtype.ext e)
    simp [Matrix.one_apply, h, h']

/-- Upper triangularity in the linear extension implies block triangularity. -/
theorem blockTriangular_of_upper {b : ι → κ} {A : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R}
    (hA : A.BlockTriangular id) : A.BlockTriangular b := by
  intro i j hij
  have hji : j ≠ i := fun h => (ne_of_lt hij) (congrArg b h)
  exact hA (lt_of_le_of_ne (block_le_of_block_lt hij) hji)

/-- Multiplication preserves the diagonal-block identity condition for block-triangular matrices. -/
theorem blockDiagonalUnitary_mul {b : ι → κ} {A B : Matrix ι ι R}
    (hAt : A.BlockTriangular b) (hBt : B.BlockTriangular b)
    (hA : BlockDiagonalUnitary A b) (hB : BlockDiagonalUnitary B b) :
    BlockDiagonalUnitary (A * B) b := by
  intro i j hij
  have hAb : A.toSquareBlock b (b i) = 1 := by
    ext r s
    calc
      A.toSquareBlock b (b i) r s = (1 : Matrix ι ι R) r s :=
        hA r s (r.property.trans s.property.symm)
      _ = (1 : Matrix (BlockIndex b (b i)) (BlockIndex b (b i)) R) r s :=
        (one_blockIndex_apply b (b i) r s).symm
  have hBb : B.toSquareBlock b (b i) = 1 := by
    ext r s
    calc
      B.toSquareBlock b (b i) r s = (1 : Matrix ι ι R) r s :=
        hB r s (r.property.trans s.property.symm)
      _ = (1 : Matrix (BlockIndex b (b i)) (BlockIndex b (b i)) R) r s :=
        (one_blockIndex_apply b (b i) r s).symm
  calc
    (A * B) i j = ((A * B).toSquareBlock b (b i)) ⟨i, rfl⟩ ⟨j, hij.symm⟩ := rfl
    _ = (A.toSquareBlock b (b i) * B.toSquareBlock b (b i)) ⟨i, rfl⟩ ⟨j, hij.symm⟩ := by
      rw [← toSquareBlock_mul_of_blockTriangular hAt hBt]
    _ = (1 : Matrix (BlockIndex b (b i)) (BlockIndex b (b i)) R) ⟨i, rfl⟩ ⟨j, hij.symm⟩ := by
      rw [hAb, hBb, Matrix.one_mul]
    _ = (1 : Matrix ι ι R) i j := one_blockIndex_apply b (b i) ⟨i, rfl⟩ ⟨j, hij.symm⟩

/-- An elementary matrix whose row lies in a strictly earlier block than its column. -/
def blockTransvection (b : ι → κ) {i j : ι} (hij : b i < b j) (a : R) :
    Matrix.GeneralLinearGroup ι R :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection (ne_of_lt hij ∘ congrArg b) a)

@[simp] theorem blockTransvection_coe (b : ι → κ) {i j : ι} (hij : b i < b j) (a : R) :
    ((blockTransvection b hij a : Matrix.GeneralLinearGroup ι R) : Matrix ι ι R) =
      Matrix.transvection i j a :=
  rfl

/-- The set of elementary maps going from a later block to an earlier one. -/
def blockTransvectionSet (b : ι → κ) : Set (Matrix.GeneralLinearGroup ι R) :=
  {g | ∃ (i j : ι) (hij : b i < b j) (a : R), g = blockTransvection b hij a}

/-- The subgroup generated by all elementary maps between distinct, ordered blocks. -/
def blockTransvectionSubgroup (b : ι → κ) : Subgroup (Matrix.GeneralLinearGroup ι R) :=
  Subgroup.closure (blockTransvectionSet (R := R) b)

/-- Every strict-block elementary matrix is the identity on each diagonal block. -/
theorem blockTransvection_blockDiagonalUnitary (b : ι → κ) {i j : ι}
    (hij : b i < b j) (a : R) : BlockDiagonalUnitary (Matrix.transvection i j a) b := by
  intro r s hrs
  by_cases h : i = r ∧ j = s
  · exact ((ne_of_lt hij) (by rw [h.1, h.2, hrs])).elim
  · simp [Matrix.transvection, Matrix.single, h]

/-- Membership in the block-unipotent kernel gives the identity formula on every diagonal block. -/
theorem blockUnipotent_diagonal {b : ι → κ} (A : blockTriangularSubgroup (R := R) b)
    (hA : A ∈ blockUnipotentSubgroup (R := R) b) :
    BlockDiagonalUnitary (A.1.1 : Matrix ι ι R) b := by
  intro i j hij
  have hker : diagonalHom b A = 1 := hA
  have hval := congrFun hker (b i)
  have he := congrArg (fun U : Matrix.GeneralLinearGroup (BlockIndex b (b i)) R =>
    U ⟨i, rfl⟩ ⟨j, hij.symm⟩) hval
  calc
    (A.1.1 : Matrix ι ι R) i j =
        (1 : Matrix (BlockIndex b (b i)) (BlockIndex b (b i)) R) ⟨i, rfl⟩ ⟨j, hij.symm⟩ := he
    _ = (1 : Matrix ι ι R) i j := one_blockIndex_apply b (b i) ⟨i, rfl⟩ ⟨j, hij.symm⟩

/-- After reindexing, a block-unipotent matrix is upper-unitriangular and retains its diagonal-block
condition. -/
theorem blockUnipotent_upperUnitriangular {b : ι → κ} (A : blockTriangularSubgroup (R := R) b)
    (hA : A ∈ blockUnipotentSubgroup (R := R) b) :
    UpperUnitriangular ((blockOrderGL b A.1 : Matrix.GeneralLinearGroup (BlockLinearOrder b) R) :
      Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) := by
  have hd := blockUnipotent_diagonal A hA
  refine ⟨?_, ?_⟩
  · intro i j hij
    rw [blockOrderGL_apply]
    by_cases hne : b i = b j
    · have h : i ≠ j := ne_of_gt hij
      calc
        (A.1.1 : Matrix ι ι R) i j = (1 : Matrix ι ι R) i j := hd i j hne
        _ = 0 := Matrix.one_apply_ne h
    · exact A.2 (block_lt_of_lt_of_ne (i := j) (j := i) (by simpa using hij) (Ne.symm hne))
  · intro i
    rw [blockOrderGL_apply]
    exact (hd i i rfl).trans (Matrix.one_apply_eq i)

/-- A clearing factor is either an allowed strict-block generator or the identity; the latter case
is exactly when its source and target lie in the same block. -/
theorem upperTransvection_mem_blockOrOne {b : ι → κ} {A : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R}
    (hA : BlockDiagonalUnitary A b) {a j : BlockLinearOrder b} (haj : a < j) :
    (upperTransvection haj (-A a j) ∈ blockTransvectionSubgroup b) ∧
      BlockDiagonalUnitary (upperTransvection haj (-A a j) : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) b := by
  by_cases hb : b a = b j
  · have hzero : A a j = 0 := (hA a j hb).trans (Matrix.one_apply_ne (ne_of_lt haj))
    have he : upperTransvection haj (-A a j) = 1 := by
      apply Units.ext
      change Matrix.transvection a j (-A a j) = 1
      rw [hzero, neg_zero, Matrix.transvection_zero]
    rw [he]
    exact ⟨Subgroup.one_mem _, blockDiagonalUnitary_one b⟩
  · have hlt : b a < b j := block_lt_of_lt_of_ne haj hb
    have he : upperTransvection haj (-A a j) = blockTransvection b hlt (-A a j) := by
      apply Units.ext
      rfl
    rw [he]
    exact ⟨Subgroup.subset_closure ⟨a, j, hlt, -A a j, rfl⟩,
      blockTransvection_blockDiagonalUnitary b hlt (-A a j)⟩

/-- The block-restricted form of `exists_rowClearing`. -/
theorem exists_blockRowClearing {b : ι → κ}
    (A : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) (hA : UpperUnitriangular A)
    (hAb : BlockDiagonalUnitary A b) (a : BlockLinearOrder b) (P s : Finset (BlockLinearOrder b))
    (haP : a ∉ P) (hs : ∀ j ∈ s, a < j)
    (hP : ∀ i ∈ P, ∀ j, A i j = (1 : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) i j) :
    ∃ T : Matrix.GeneralLinearGroup (BlockLinearOrder b) R,
      T ∈ blockTransvectionSubgroup b ∧
      UpperUnitriangular (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) ∧
      BlockDiagonalUnitary (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) b ∧
      (∀ i ∈ P, ∀ j, (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) i j =
        (1 : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) i j) ∧
      (∀ j, (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) a j =
        if j ∈ s then 0 else A a j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, Subgroup.one_mem _, upperUnitriangular_one, blockDiagonalUnitary_one b, ?_, ?_⟩
      · simpa only [Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one] using hP
      · simp
  | @insert j s hj ih =>
      have haj : a < j := hs j (Finset.mem_insert_self _ _)
      have hs' : ∀ q ∈ s, a < q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      obtain ⟨T, hT, hTu, hTd, hP', hrow⟩ := ih hs'
      let E := upperTransvection haj (-A a j)
      obtain ⟨hE, hEd⟩ := upperTransvection_mem_blockOrOne hAb haj
      have hEu : UpperUnitriangular (E : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) :=
        upperTransvection_upperUnitriangular haj _
      have hTj : (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) a j = A a j := by
        rw [hrow, if_neg hj]
      have hTa : (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) a a = 1 := by
        rw [hrow]
        have ha : a ∉ s := fun h => (hs a (Finset.mem_insert_of_mem h)).false
        simp [ha, hA.2]
      refine ⟨T * E, mul_mem hT hE, upperUnitriangular_mul hTu hEu,
        blockDiagonalUnitary_mul (blockTriangular_of_upper hTu.1) (blockTriangular_of_upper hEu.1)
          hTd hEd, ?_, ?_⟩
      · intro i hi q
        simp only [E, Matrix.GeneralLinearGroup.coe_mul, upperTransvection_coe,
          ← Matrix.mul_assoc]
        have hia : i ≠ a := fun h => haP (h ▸ hi)
        have hid : (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) i a = 0 := by
          rw [hP' i hi, Matrix.one_apply, if_neg hia]
        by_cases hq : q = j
        · subst q
          change (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) *
            Matrix.transvection a j (-A a j)) i j = _
          rw [Matrix.mul_transvection_apply_same, hP' i hi, hid]
          simp
        · change (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) *
            Matrix.transvection a j (-A a j)) i q = _
          rw [Matrix.mul_transvection_apply_of_ne a j i q hq]
          exact hP' i hi q
      · intro q
        simp only [E, Matrix.GeneralLinearGroup.coe_mul, upperTransvection_coe,
          ← Matrix.mul_assoc]
        by_cases hq : q = j
        · subst q
          change (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) *
            Matrix.transvection a j (-A a j)) a j = _
          rw [Matrix.mul_transvection_apply_same, hTj, hTa]
          simp
        · change (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) *
            Matrix.transvection a j (-A a j)) a q = _
          rw [Matrix.mul_transvection_apply_of_ne a j a q hq, hrow]
          by_cases hqs : q ∈ s <;> simp [hqs, hq]

/-- Clear one row using only strict-block elementary maps and identity factors. -/
theorem exists_blockClearRow {b : ι → κ}
    (A : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) (hA : UpperUnitriangular A)
    (hAb : BlockDiagonalUnitary A b) (a : BlockLinearOrder b) (P : Finset (BlockLinearOrder b))
    (haP : a ∉ P)
    (hP : ∀ i ∈ P, ∀ j, A i j = (1 : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) i j) :
    ∃ T : Matrix.GeneralLinearGroup (BlockLinearOrder b) R,
      T ∈ blockTransvectionSubgroup b ∧
      UpperUnitriangular (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) ∧
      BlockDiagonalUnitary (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) b ∧
      (∀ i ∈ insert a P, ∀ j, (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) i j =
        (1 : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) i j) := by
  classical
  let s := Finset.univ.filter fun j => a < j
  obtain ⟨T, hT, hTu, hTd, hP', hrow⟩ :=
    exists_blockRowClearing A hA hAb a P s haP (fun _ h => (Finset.mem_filter.mp h).2) hP
  refine ⟨T, hT, hTu, hTd, fun i hi q => ?_⟩
  rcases Finset.mem_insert.mp hi with hia | hi
  · subst i
    rw [hrow]
    by_cases haq : a < q
    · have hmem : q ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, haq⟩
      simp [hmem, ne_of_lt haq]
    · have hnot : q ∉ s := fun h => haq (Finset.mem_filter.mp h).2
      rw [if_neg hnot]
      by_cases hqa : q = a
      · subst q
        simp [hA.2]
      · have hqa' : q < a := lt_of_le_of_ne (le_of_not_gt haq) hqa
        rw [hA.1 (by simpa using hqa'), Matrix.one_apply, if_neg (Ne.symm hqa)]
  · exact hP' i hi q

/-- Block-unipotent matrices reduce to the identity under right multiplication by strict-block
transvections. -/
theorem exists_blockTransvection_reduction {b : ι → κ}
    (A : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) (hA : UpperUnitriangular A)
    (hAb : BlockDiagonalUnitary A b) :
    ∃ T : Matrix.GeneralLinearGroup (BlockLinearOrder b) R,
      T ∈ blockTransvectionSubgroup b ∧
      UpperUnitriangular (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) ∧
      BlockDiagonalUnitary (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) b ∧
      A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) = 1 := by
  classical
  have hrows : ∀ s : Finset (BlockLinearOrder b),
      ∃ T : Matrix.GeneralLinearGroup (BlockLinearOrder b) R,
        T ∈ blockTransvectionSubgroup b ∧
        UpperUnitriangular (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) ∧
        BlockDiagonalUnitary (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) b ∧
        (∀ i ∈ s, ∀ j, (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) i j =
          (1 : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) i j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨1, Subgroup.one_mem _, upperUnitriangular_one, blockDiagonalUnitary_one b, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨T, hT, hTu, hTd, hP⟩ := ih
        have hAT : UpperUnitriangular (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) :=
          upperUnitriangular_mul hA hTu
        have hATd : BlockDiagonalUnitary
            (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) b :=
          blockDiagonalUnitary_mul (blockTriangular_of_upper hA.1) (blockTriangular_of_upper hTu.1)
            hAb hTd
        obtain ⟨E, hE, hEu, hEd, hclear⟩ := exists_blockClearRow
          (A * (T : Matrix (BlockLinearOrder b) (BlockLinearOrder b) R)) hAT hATd a s ha hP
        refine ⟨T * E, mul_mem hT hE, upperUnitriangular_mul hTu hEu,
          blockDiagonalUnitary_mul (blockTriangular_of_upper hTu.1) (blockTriangular_of_upper hEu.1)
            hTd hEd, ?_⟩
        simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_assoc] using hclear
  obtain ⟨T, hT, hTu, hTd, hclear⟩ := hrows Finset.univ
  exact ⟨T, hT, hTu, hTd, Matrix.ext fun i j => hclear i (Finset.mem_univ i) j⟩

/-- A block-triangular element belongs to the unipotent kernel when its diagonal blocks are all the
identity. -/
theorem mem_blockUnipotent_of_diagonal {b : ι → κ}
    (A : blockTriangularSubgroup (R := R) b)
    (hA : BlockDiagonalUnitary (A.1.1 : Matrix ι ι R) b) :
    A ∈ blockUnipotentSubgroup (R := R) b := by
  change diagonalHom b A = 1
  funext k
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  calc
    diagonalHom b A k i j = (A.1.1 : Matrix ι ι R) i j := rfl
    _ = (1 : Matrix ι ι R) i j := hA i j (i.property.trans j.property.symm)
    _ = (1 : Matrix (BlockIndex b k) (BlockIndex b k) R) i j :=
      (one_blockIndex_apply b k i j).symm

/-- Every strict-block generator belongs to the ambient image of the unipotent kernel. -/
theorem blockTransvection_mem_unipotent_map {b : ι → κ} {i j : ι}
    (hij : b i < b j) (a : R) :
    blockTransvection b hij a ∈ (blockUnipotentSubgroup (R := R) b).map
      (blockTriangularSubgroup (R := R) b).subtype := by
  let A : blockTriangularSubgroup (R := R) b :=
    ⟨blockTransvection b hij a, Matrix.blockTriangular_transvection hij.le a⟩
  refine ⟨A, ?_, rfl⟩
  exact mem_blockUnipotent_of_diagonal A (blockTransvection_blockDiagonalUnitary b hij a)

/-- The generated strict-block subgroup is contained in the ambient unipotent kernel. -/
theorem blockTransvectionSubgroup_le_unipotent_map (b : ι → κ) :
    blockTransvectionSubgroup (R := R) b ≤ (blockUnipotentSubgroup (R := R) b).map
      (blockTriangularSubgroup (R := R) b).subtype := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, j, hij, a, rfl⟩
  exact blockTransvection_mem_unipotent_map hij a

/-- Every element of the block-unipotent kernel belongs to the subgroup generated by the strict-block
transvections. -/
theorem blockUnipotent_mem_blockTransvectionSubgroup {b : ι → κ}
    (A : blockTriangularSubgroup (R := R) b) (hA : A ∈ blockUnipotentSubgroup (R := R) b) :
    A.1 ∈ blockTransvectionSubgroup (R := R) b := by
  have hu := blockUnipotent_upperUnitriangular A hA
  have hd : BlockDiagonalUnitary
      ((blockOrderGL b A.1 : Matrix.GeneralLinearGroup (BlockLinearOrder b) R) :
        Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) b := by
    intro i j hij
    rw [blockOrderGL_apply]
    exact blockUnipotent_diagonal A hA i j hij
  obtain ⟨T, hT, -, -, hAT⟩ := exists_blockTransvection_reduction
    ((blockOrderGL b A.1 : Matrix.GeneralLinearGroup (BlockLinearOrder b) R) :
      Matrix (BlockLinearOrder b) (BlockLinearOrder b) R) hu hd
  have hsymm : (blockOrderGL b).symm T ∈ blockTransvectionSubgroup (R := R) b := by
    refine Subgroup.closure_induction
      (p := fun x _ => (blockOrderGL b).symm x ∈ blockTransvectionSubgroup (R := R) b) ?_
      (by simp) (fun x y _ _ hx hy => by simpa using mul_mem hx hy)
      (fun x _ hx => by simpa using Subgroup.inv_mem _ hx) hT
    rintro x ⟨i, j, hij, a, rfl⟩
    have he : (blockOrderGL b).symm (blockTransvection b hij a) = blockTransvection b hij a := by
      apply Matrix.GeneralLinearGroup.ext
      intro r s
      rfl
    exact he.symm ▸ Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩
  have hred : blockOrderGL b A.1 * T = 1 := Units.ext hAT
  have hinv : blockOrderGL b A.1 = T⁻¹ := eq_inv_of_mul_eq_one_left hred
  have heq : A.1 = (blockOrderGL b).symm T⁻¹ := by
    calc
      A.1 = (blockOrderGL b).symm (blockOrderGL b A.1) := (blockOrderGL b).symm_apply_apply A.1 |>.symm
      _ = (blockOrderGL b).symm T⁻¹ := congrArg (blockOrderGL b).symm hinv
  rw [heq]
  simpa using Subgroup.inv_mem _ hsymm

/-- The unipotent kernel, viewed inside the full general-linear group, is exactly the subgroup
generated by the strict-block transvections. -/
theorem blockUnipotent_map_eq_blockTransvectionSubgroup (b : ι → κ) :
    (blockUnipotentSubgroup (R := R) b).map (blockTriangularSubgroup (R := R) b).subtype =
      blockTransvectionSubgroup (R := R) b := by
  apply le_antisymm
  · rintro x ⟨A, hA, rfl⟩
    exact blockUnipotent_mem_blockTransvectionSubgroup A hA
  · exact blockTransvectionSubgroup_le_unipotent_map b

end BlockGeneration

end LeanCategories.Modules
