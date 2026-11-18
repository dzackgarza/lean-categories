/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Folding
public import LeanCategories.Lattices.Valued.Standard
public import Mathlib.Data.Matrix.Basis

/-!
# Folding `T_dP` to `T_En`: the worked instance of AEGS §3.7

Alexeev, Engel, Garza and Schaffler, *Compact moduli of Enriques surfaces of degree 2*,
Nagoya Math. J. 259 (2025), arXiv:2312.03638v2, §3.7 (printed pp. 11–12), work with the lattice

`T_dP = U ⊕ U(2) ⊕ E₈ ⊕ E₈`, of rank `20` and signature `(2,18)`,

and the involution `I = -I_En` of it whose invariant part is the lattice `T_En = U ⊕ U(2) ⊕ E₈(2)`
(their Lemma 3.4: "Consider the lattice `T_dP` with the involution `I := -I_En …`, so that
`T_dP^{I=1} = T_En`"). This file builds that lattice from the block Gram matrix
(`tdpBlockGram`, `tdpLattice`), the involution as an element of the orthogonal group
(`tdpIsometry`, `tdpIsometry_mul_self`), and proves the two statements of the source that the
five folded diagrams of §3.8 rest on:

* `tdpIsometry_fixed_iff`: the invariant sublattice is the locus `e' = -e` of the two `E₈` blocks,
  i.e. `U ⊕ U(2) ⊕ Δ⁻(E₈)`, which is `U(2) ⊕ E₈(2)` up to the diagonal — the source's
  `T_dP^{I=1} = T_En`.
* `tdp_pairing_involution_self`: the source's displayed identity in the proof of Lemma 3.4,
  `α · I α = α² − (e + e')²`.
* `tdp_fold_square_of_orthogonal`: the case (3) conclusion of Lemma 3.4 — a vector of square `-2`
  orthogonal to its image has folded square `-4`, so it folds to a root of `T_En` and not of
  `T_dP`; it is the arithmetic that tells the five folded diagrams of the source which vertices
  survive the folding (`foldedRootSet` drops the ones whose fold vanishes).

The folded *diagrams* themselves (Figures 7, 8 of the source; Sterk's diagrams) are printed as
pictures and their nineteen- and twenty-two-vertex input diagrams are not tabulated in the text,
so only the folding arithmetic that produces them is formalized here; see the module docstring of
`Folding.lean` for the chamber-level theorem that the diagrams then feed.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces with a
  numerical polarization of degree 2*, Nagoya Math. J. 259 (2025), §3.7, Lemma 3.4 (printed
  pp. 11–12) and (4), the relation in `U ⊕ E₈²` (printed p. 11).
* E. B. Vinberg, *The groups of unit elements of certain quadratic forms*, Mat. Sb. 87 (1972), §1.

## LC-09 record

Searched the repository and Mathlib at the pinned head for the block lattices and for a matrix
splitting lemma before writing anything: `rg "hyperbolicPlaneGramMatrix|e8GramMatrix"` (both in
`Lattices/Valued/Standard.lean`, with `hyperbolicPlaneGramMatrix_isSymm`, `e8GramMatrix_isSymm`,
`e8GramMatrix_det`); `rg "toBilin'_fromBlocks|toBilin'_apply"` (no block-splitting lemma for
`Matrix.toBilin'` exists in Mathlib or here, so `toBilin'_fromBlocks_zero_apply` is proved
below); `rg "enriques|folding"` over `LeanCategories/` (nothing); `corpus/ambiguity-resolution-
source-map-for-issues-1-and-4.md` §I (the source ruling: "ADE->BC foldings via involutions",
invariants not coinvariants).
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-! ## Splitting a bilinear form into two blocks -/

theorem toBilin'_fromBlocks_zero_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℤ) (B : Matrix κ κ ℤ) (x y : ι ⊕ κ → ℤ) :
    Matrix.toBilin' (Matrix.fromBlocks A 0 0 B) x y
      = Matrix.toBilin' A (fun i => x (Sum.inl i)) (fun i => y (Sum.inl i))
        + Matrix.toBilin' B (fun k => x (Sum.inr k)) (fun k => y (Sum.inr k)) := by
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply, Matrix.toBilin'_apply,
    Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add]

theorem toBilin'_add_left {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (u v w : ι → ℤ) :
    Matrix.toBilin' M (u + v) w = Matrix.toBilin' M u w + Matrix.toBilin' M v w := by
  rw [map_add]
  rfl

theorem toBilin'_add_right {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (u v w : ι → ℤ) :
    Matrix.toBilin' M u (v + w) = Matrix.toBilin' M u v + Matrix.toBilin' M u w := by
  rw [map_add]

theorem toBilin'_neg_left {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (u v : ι → ℤ) :
    Matrix.toBilin' M (-u) v = -Matrix.toBilin' M u v := by
  rw [map_neg, LinearMap.neg_apply]

theorem toBilin'_neg_right {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (u v : ι → ℤ) :
    Matrix.toBilin' M u (-v) = -Matrix.toBilin' M u v := by
  rw [map_neg]

theorem toBilin'_neg_fun_left {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (u v : ι → ℤ) :
    Matrix.toBilin' M (fun i => -u i) v = -Matrix.toBilin' M u v := by
  rw [show (fun i => -u i) = -u from rfl, toBilin'_neg_left]

theorem toBilin'_neg_fun_right {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (u v : ι → ℤ) :
    Matrix.toBilin' M u (fun i => -v i) = -Matrix.toBilin' M u v := by
  rw [show (fun i => -v i) = -v from rfl, toBilin'_neg_right]

theorem toBilin'_add_fun_left {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (u v w : ι → ℤ) :
    Matrix.toBilin' M (fun i => u i + v i) w = Matrix.toBilin' M u w + Matrix.toBilin' M v w := by
  rw [show (fun i => u i + v i) = u + v from rfl, toBilin'_add_left]

theorem toBilin'_add_fun_right {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (u v w : ι → ℤ) :
    Matrix.toBilin' M u (fun i => v i + w i) = Matrix.toBilin' M u v + Matrix.toBilin' M u w := by
  rw [show (fun i => v i + w i) = v + w from rfl, toBilin'_add_right]

theorem toBilin'_symm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (hM : M.IsSymm) (u v : ι → ℤ) :
    Matrix.toBilin' M u v = Matrix.toBilin' M v u := by
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hM.apply j i]
  ring

/-! ## The lattice `T_dP = U ⊥ U(2) ⊥ E₈ ⊥ E₈` -/

/-- The block index of `T_dP`: `U`, then `U(2)`, then the two `E₈` summands. -/
abbrev TdpIndex : Type := (Fin 2 ⊕ Fin 2) ⊕ (Fin 8 ⊕ Fin 8)

/-- The `U ⊥ U(2)` block. -/
noncomputable def tdpU2Gram : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  Matrix.fromBlocks hyperbolicPlaneGramMatrix 0 0 ((2 : ℤ) • hyperbolicPlaneGramMatrix)

/-- The `E₈ ⊥ E₈` block. -/
noncomputable def tdpE8Gram : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℤ :=
  Matrix.fromBlocks e8GramMatrix 0 0 e8GramMatrix

/-- The Gram matrix of `T_dP = U ⊥ U(2) ⊥ E₈ ⊥ E₈`. -/
noncomputable def tdpBlockGram : Matrix TdpIndex TdpIndex ℤ :=
  Matrix.fromBlocks tdpU2Gram 0 0 tdpE8Gram

theorem tdpU2Gram_inl_inl (a b : Fin 2) :
    tdpU2Gram (Sum.inl a) (Sum.inl b) = hyperbolicPlaneGramMatrix a b := by
  rw [tdpU2Gram, Matrix.fromBlocks_apply₁₁]

theorem tdpU2Gram_inl_inr (a b : Fin 2) : tdpU2Gram (Sum.inl a) (Sum.inr b) = 0 := by
  rw [tdpU2Gram, Matrix.fromBlocks_apply₁₂]
  rfl

theorem tdpU2Gram_inr_inl (a b : Fin 2) : tdpU2Gram (Sum.inr a) (Sum.inl b) = 0 := by
  rw [tdpU2Gram, Matrix.fromBlocks_apply₂₁]
  rfl

theorem tdpU2Gram_inr_inr (a b : Fin 2) :
    tdpU2Gram (Sum.inr a) (Sum.inr b) = 2 * hyperbolicPlaneGramMatrix a b := by
  rw [tdpU2Gram, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]

theorem tdpE8Gram_inl_inl (a b : Fin 8) :
    tdpE8Gram (Sum.inl a) (Sum.inl b) = e8GramMatrix a b := by
  rw [tdpE8Gram, Matrix.fromBlocks_apply₁₁]

theorem tdpE8Gram_inl_inr (a b : Fin 8) : tdpE8Gram (Sum.inl a) (Sum.inr b) = 0 := by
  rw [tdpE8Gram, Matrix.fromBlocks_apply₁₂]
  rfl

theorem tdpE8Gram_inr_inl (a b : Fin 8) : tdpE8Gram (Sum.inr a) (Sum.inl b) = 0 := by
  rw [tdpE8Gram, Matrix.fromBlocks_apply₂₁]
  rfl

theorem tdpE8Gram_inr_inr (a b : Fin 8) :
    tdpE8Gram (Sum.inr a) (Sum.inr b) = e8GramMatrix a b := by
  rw [tdpE8Gram, Matrix.fromBlocks_apply₂₂]

theorem tdpBlockGram_inl_inl (a b : Fin 2 ⊕ Fin 2) :
    tdpBlockGram (Sum.inl a) (Sum.inl b) = tdpU2Gram a b := by
  rw [tdpBlockGram, Matrix.fromBlocks_apply₁₁]

theorem tdpBlockGram_inl_inr (a : Fin 2 ⊕ Fin 2) (b : Fin 8 ⊕ Fin 8) :
    tdpBlockGram (Sum.inl a) (Sum.inr b) = 0 := by
  rw [tdpBlockGram, Matrix.fromBlocks_apply₁₂]
  rfl

theorem tdpBlockGram_inr_inl (a : Fin 8 ⊕ Fin 8) (b : Fin 2 ⊕ Fin 2) :
    tdpBlockGram (Sum.inr a) (Sum.inl b) = 0 := by
  rw [tdpBlockGram, Matrix.fromBlocks_apply₂₁]
  rfl

theorem tdpBlockGram_inr_inr (a b : Fin 8 ⊕ Fin 8) :
    tdpBlockGram (Sum.inr a) (Sum.inr b) = tdpE8Gram a b := by
  rw [tdpBlockGram, Matrix.fromBlocks_apply₂₂]

theorem tdpU2Gram_isSymm : tdpU2Gram.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · rw [tdpU2Gram_inl_inl, tdpU2Gram_inl_inl, hyperbolicPlaneGramMatrix_isSymm.apply]
  · rw [tdpU2Gram_inr_inl, tdpU2Gram_inl_inr]
  · rw [tdpU2Gram_inl_inr, tdpU2Gram_inr_inl]
  · rw [tdpU2Gram_inr_inr, tdpU2Gram_inr_inr, hyperbolicPlaneGramMatrix_isSymm.apply]

theorem tdpE8Gram_isSymm : tdpE8Gram.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · rw [tdpE8Gram_inl_inl, tdpE8Gram_inl_inl, e8GramMatrix_isSymm.apply]
  · rw [tdpE8Gram_inr_inl, tdpE8Gram_inl_inr]
  · rw [tdpE8Gram_inl_inr, tdpE8Gram_inr_inl]
  · rw [tdpE8Gram_inr_inr, tdpE8Gram_inr_inr, e8GramMatrix_isSymm.apply]

theorem tdpBlockGram_isSymm : tdpBlockGram.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · rw [tdpBlockGram_inl_inl, tdpBlockGram_inl_inl, tdpU2Gram_isSymm.apply]
  · rw [tdpBlockGram_inr_inl, tdpBlockGram_inl_inr]
  · rw [tdpBlockGram_inl_inr, tdpBlockGram_inr_inl]
  · rw [tdpBlockGram_inr_inr, tdpBlockGram_inr_inr, tdpE8Gram_isSymm.apply]

/-- The lattice `T_dP = U ⊕ U(2) ⊕ E₈ ⊕ E₈` of AEGS §2.3. -/
noncomputable def tdpLattice : IntegralLatticeCat ℤ := by
  refine ⟨BilinModuleCat.ofBilinMap (Matrix.toBilin' tdpBlockGram), ?_, ?_⟩
  · change Module.Projective ℤ (TdpIndex → ℤ)
    infer_instance
  · intro x y
    exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr tdpBlockGram_isSymm).eq x y

/-- `T_dP` as a finite projective lattice. -/
noncomputable def tdpFiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ := by
  refine ⟨tdpLattice, ?_⟩
  change Module.Finite ℤ (TdpIndex → ℤ)
  infer_instance

@[simp] theorem tdpLattice_pairing (x y : tdpFiniteLattice.obj.obj.carrier) :
    tdpFiniteLattice.obj.obj.pairing x y = Matrix.toBilin' tdpBlockGram x y := rfl

/-! ## The involution `I = -I_En` -/

/-- The involution `I = -I_En` of AEGS Lemma 3.4: the identity on `U ⊕ U(2)` and
`(e, e') ↦ (-e', -e)` on the two `E₈` summands. -/
def tdpSwapSign (x : TdpIndex → ℤ) : TdpIndex → ℤ :=
  Sum.elim (fun c => x (Sum.inl c))
    (Sum.elim (fun j => -x (Sum.inr (Sum.inr j)))
      (fun j => -x (Sum.inr (Sum.inl j))))

@[simp] theorem tdpSwapSign_inl (x : TdpIndex → ℤ) (c : Fin 2 ⊕ Fin 2) :
    tdpSwapSign x (Sum.inl c) = x (Sum.inl c) := rfl

@[simp] theorem tdpSwapSign_inr_inl (x : TdpIndex → ℤ) (j : Fin 8) :
    tdpSwapSign x (Sum.inr (Sum.inl j)) = -x (Sum.inr (Sum.inr j)) := rfl

@[simp] theorem tdpSwapSign_inr_inr (x : TdpIndex → ℤ) (j : Fin 8) :
    tdpSwapSign x (Sum.inr (Sum.inr j)) = -x (Sum.inr (Sum.inl j)) := rfl

theorem tdpSwapSign_add (x y : TdpIndex → ℤ) :
    tdpSwapSign (x + y) = tdpSwapSign x + tdpSwapSign y := by
  funext c
  rcases c with c | j | j
  · simp [Pi.add_apply]
  · rw [Pi.add_apply, tdpSwapSign_inr_inl, tdpSwapSign_inr_inl, tdpSwapSign_inr_inl,
      Pi.add_apply, neg_add]
  · rw [Pi.add_apply, tdpSwapSign_inr_inr, tdpSwapSign_inr_inr, tdpSwapSign_inr_inr,
      Pi.add_apply, neg_add]

theorem tdpSwapSign_smul (r : ℤ) (x : TdpIndex → ℤ) :
    tdpSwapSign (r • x) = r • tdpSwapSign x := by
  funext c
  rcases c with c | j | j <;> simp [Pi.smul_apply]

theorem tdpSwapSign_involutive (x : TdpIndex → ℤ) : tdpSwapSign (tdpSwapSign x) = x := by
  funext c
  rcases c with c | j | j <;> simp

noncomputable def tdpSwapSignEquiv : (TdpIndex → ℤ) ≃ₗ[ℤ] (TdpIndex → ℤ) where
  toFun := tdpSwapSign
  invFun := tdpSwapSign
  left_inv := tdpSwapSign_involutive
  right_inv := tdpSwapSign_involutive
  map_add' := tdpSwapSign_add
  map_smul' := tdpSwapSign_smul

theorem tdpSwapSign_pairing (x y : TdpIndex → ℤ) :
    Matrix.toBilin' tdpBlockGram (tdpSwapSign x) (tdpSwapSign y)
      = Matrix.toBilin' tdpBlockGram x y := by
  simp only [tdpBlockGram, tdpU2Gram, tdpE8Gram, toBilin'_fromBlocks_zero_apply,
    tdpSwapSign_inl, tdpSwapSign_inr_inl, tdpSwapSign_inr_inr, toBilin'_neg_fun_left,
    toBilin'_neg_fun_right]
  abel

/-- The involution `I = -I_En` of `T_dP` as an element of the orthogonal group. -/
noncomputable def tdpIsometry : OrthogonalGroup tdpFiniteLattice.obj :=
  ⟨tdpSwapSignEquiv, tdpSwapSign_pairing⟩

@[simp] theorem tdpIsometry_apply (x : tdpFiniteLattice.obj.obj.carrier) :
    tdpIsometry.1 x = tdpSwapSign x := rfl

theorem tdpIsometry_mul_self : tdpIsometry * tdpIsometry = 1 := by
  apply Subtype.ext
  ext x
  change tdpSwapSign (tdpSwapSign x) = x
  exact tdpSwapSign_involutive x

/-! ## The invariant sublattice `T_En` and the arithmetic of AEGS Lemma 3.4 -/

/-- The `U ⊕ U(2)` part of a vector of `T_dP`. -/
abbrev tdpFirst (x : TdpIndex → ℤ) : Fin 2 ⊕ Fin 2 → ℤ := fun c => x (Sum.inl c)

/-- The first `E₈` block of a vector of `T_dP`. -/
abbrev tdpE8First (x : TdpIndex → ℤ) : Fin 8 → ℤ := fun j => x (Sum.inr (Sum.inl j))

/-- The second `E₈` block of a vector of `T_dP`. -/
abbrev tdpE8Second (x : TdpIndex → ℤ) : Fin 8 → ℤ := fun j => x (Sum.inr (Sum.inr j))

/-- **`T_dP^{I=1} = T_En`** (AEGS Lemma 3.4), function form: the vectors fixed by `I` are the
locus `e' = -e` on the two `E₈` blocks. -/
theorem tdpSwapSign_fixed_iff (x : TdpIndex → ℤ) :
    tdpSwapSign x = x ↔ ∀ j, x (Sum.inr (Sum.inr j)) = -x (Sum.inr (Sum.inl j)) := by
  constructor
  · intro h j
    have h1 : -x (Sum.inr (Sum.inr j)) = x (Sum.inr (Sum.inl j)) := by
      have hc := congrFun h (Sum.inr (Sum.inl j))
      rwa [tdpSwapSign_inr_inl] at hc
    exact (neg_eq_iff_eq_neg).mp h1
  · intro h
    funext c
    rcases c with c | j | j
    · rfl
    · rw [tdpSwapSign_inr_inl, h j, neg_neg]
    · rw [tdpSwapSign_inr_inr, h j]

/-- **`T_dP^{I=1} = T_En`**: the invariant sublattice of `I = -I_En` is `U ⊕ U(2) ⊕ Δ⁻(E₈)`,
i.e. `U(2) ⊕ E₈(2)` — the fixed locus of the two `E₈` blocks is their anti-diagonal. -/
theorem tdpIsometry_fixed_iff (x : tdpFiniteLattice.obj.obj.carrier) :
    x ∈ involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry ↔
      ∀ j, x (Sum.inr (Sum.inr j)) = -x (Sum.inr (Sum.inl j)) := by
  rw [mem_involutionFixedSubmodule_iff, tdpIsometry_apply]
  exact tdpSwapSign_fixed_iff x

/-- The folded vector `α + I α` of a non-fixed vector lies in the invariant sublattice. -/
theorem tdpSwapSign_fold_fixed (x : TdpIndex → ℤ) :
    tdpSwapSign (x + tdpSwapSign x) = x + tdpSwapSign x := by
  funext c
  rcases c with c | (i | i) | (j | j) <;>
    simp [Pi.add_apply]

/-- **AEGS Lemma 3.4's identity** `α · I α = α² − (e + e')²`. -/
theorem tdp_pairing_involution_self (x : TdpIndex → ℤ) :
    Matrix.toBilin' tdpBlockGram x (tdpSwapSign x)
      = Matrix.toBilin' tdpBlockGram x x
        - Matrix.toBilin' e8GramMatrix (tdpE8First x + tdpE8Second x)
            (tdpE8First x + tdpE8Second x) := by
  simp only [tdpBlockGram, tdpU2Gram, tdpE8Gram, toBilin'_fromBlocks_zero_apply,
    tdpSwapSign_inl, tdpSwapSign_inr_inl, tdpSwapSign_inr_inr, toBilin'_neg_fun_right,
    toBilin'_add_left, toBilin'_add_right]
  rw [show Matrix.toBilin' e8GramMatrix (fun i => x (Sum.inr (Sum.inr i)))
        (fun i => x (Sum.inr (Sum.inl i)))
      = Matrix.toBilin' e8GramMatrix (fun i => x (Sum.inr (Sum.inl i)))
        (fun i => x (Sum.inr (Sum.inr i))) from
    toBilin'_symm e8GramMatrix e8GramMatrix_isSymm _ _]
  ring

/-- **AEGS Lemma 3.4, case (3)**: a vector of square `-2` orthogonal to its image folds to a
vector of square `-4` in the invariant sublattice `T_En` — a root of `T_En` that is not a root of
`T_dP`. The folded vector is `α + I α` (AEGS Definition 3.3), and it is `I`-fixed
(`tdpSwapSign_fold_fixed`). -/
theorem tdp_fold_square_of_orthogonal (x : TdpIndex → ℤ)
    (h2 : Matrix.toBilin' tdpBlockGram x x = -2)
    (h0 : Matrix.toBilin' tdpBlockGram x (tdpSwapSign x) = 0) :
    Matrix.toBilin' tdpBlockGram (x + tdpSwapSign x) (x + tdpSwapSign x) = -4 := by
  have hexp : Matrix.toBilin' tdpBlockGram (x + tdpSwapSign x) (x + tdpSwapSign x)
      = Matrix.toBilin' tdpBlockGram x x
        + 2 * Matrix.toBilin' tdpBlockGram x (tdpSwapSign x)
        + Matrix.toBilin' tdpBlockGram (tdpSwapSign x) (tdpSwapSign x) := by
    rw [toBilin'_add_left, toBilin'_add_right, toBilin'_add_right,
      toBilin'_symm tdpBlockGram tdpBlockGram_isSymm (tdpSwapSign x) x]
    ring
  have hiso : Matrix.toBilin' tdpBlockGram (tdpSwapSign x) (tdpSwapSign x)
      = Matrix.toBilin' tdpBlockGram x x := tdpSwapSign_pairing x x
  rw [hexp, hiso, h2, h0]
  ring

end LeanCategories.Lattices.Valued
