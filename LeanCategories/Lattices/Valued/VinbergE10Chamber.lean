/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.WeylChambers
public import LeanCategories.Lattices.Valued.Standard
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Vinberg chamber of `E₁₀(2)`

`E₁₀ = U ⊥ E₈` is the even unimodular lattice `II_{1,9}` of signature `(1,9)`; `E₁₀(2)` is the
same `ℤ`-module with the form doubled (`sage-preamble-definition-catalogue`, the named lattices
`E10 = U ⊕ E8`, `E10(2)`). This file builds `E₁₀(2)` from that block definition, exhibits the ten
simple roots of the `E₁₀` diagram inside it as a `ℤ`-basis, and verifies the three fields of
`IsChamberWithWalls` for that root set — the chamber of `W(E₁₀(2))`.

## The data and what is checked

* `e10Cartan` is the Cartan matrix of the `E₁₀` diagram in the node order
  `α₀, α₁, …, α₈, α₋₁` (node `0` the affine node of `E₉ = E₁₀ ∖ {α₋₁}`, nodes `1..8` the `E₈`
  simple roots in the repository's `e8GramMatrix` order, node `9` the hyperbolic extension).
  Its determinant `-1` is computed, not assumed.
* `e10BlockGram` is the Gram matrix of `E₁₀(2) = 2 · (U ⊥ E₈)` in the block basis; its
  determinant `-2¹⁰`, its signature `(1,9)` and its evenness are computed from it
  (`e10BlockGram_det`, `e10BlockGram_signature`, `e10BlockGram_even`).
* `e10Root i` are the ten simple roots as block vectors; `e10Root_inverse` inverts their
  coordinate matrix, so they are a `ℤ`-basis (`e10Root_basis`), and `e10Root_pairing` computes
  their Gram matrix as `-2 · e10Cartan`. Each is a reflective root of negative square
  (`e10Root_isReflectiveRoot`, `e10Root_negSquare`).
* `e10InteriorPoint` is a lattice vector pairing `2` with every simple root and having positive
  square `2480`, so the interior cone of the root set is nonempty (`e10_interior_nonempty`).

## The criterion

`isChamberWithWalls_of_signs` is the general criterion: for **any** integral lattice `L` of
signature `(1,n)` and any finite root family `R` whose interior cone is nonempty, if every
negative reflective root of `L` is a `ℤ`-combination of `R` whose coordinates all have the same
sign, then `C(R)` is a chamber with walls `R`. The proof of the third field is the observation
that a same-sign combination pairs strictly one way with every point of the interior cone
(`pairing_ne_zero_of_signs`).

For `E₁₀(2)` the sign hypothesis is the arithmetic statement `e10_signs`: a `ℤ`-vector `b` with
`b ⬝ᵥ (C b) = 2` — the square of a root of `E₁₀(2)` — has all coordinates of one sign. It is the
content of `e10_not_mixed`.

## References

* È. B. Vinberg, *The groups of unit elements of certain quadratic forms*, Mat. Sb. 87 (1972),
  §3.2 (Propositions 4 and 5) for the algorithm and the completeness of a wall set.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.3, for
  the finite-type argument that every root is a nonnegative integer combination of the simple
  ones — the statement `e10_signs` extends to the hyperbolic diagram `E₁₀`.
* The named-lattice catalogue `site/catalogues/sage-preamble-definition-catalogue.md` for
  `E10 = U ⊕ E8` and `E10(2)`.

## LC-09 record

Searched (Mathlib source at the pinned head, and the formalization corpus):
`content:IsCoxeter`, `content:fundamental domain reflection`,
`content:hyperbolic polyhedron finite volume`, `content:Vinberg`, `content:IsChamberWithWalls`,
`file:LinearAlgebra/RootSystem/Chamber`, plus local greps for `IsCoxeter`, `fundamentalDomain`,
`chamber` over `Mathlib/`. Hits: Mathlib's `CoxeterMatrix`/`CoxeterSystem` (combinatorial), its
`MeasureTheory/Group/FundamentalDomain` (measurable, not polyhedral), Atlas's
`HyperplaneArrangement`/`ReflectionGroup` (affine arrangements), and TauCeti's
`LinearAlgebra/RootSystem/Chamber.lean` (finite root systems: the dominant chamber is cut out by
the *simple* coroots because every positive root is a nonnegative integer combination of them).
Nothing in the corpus states the completeness of a wall set for a Lorentzian lattice, and nothing
is ported: the mechanism TauCeti uses for finite type is exactly what `e10_signs` establishes for
the hyperbolic diagram `E₁₀`, and the finite-type statement is already the starting point of
`WeylChambers.lean`.
-/

@[expose] public section

open Matrix
open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued
open scoped BigOperators

namespace LeanCategories.Lattices.Valued

/-! ## The `E₁₀` diagram -/

/-- The nine edges of the `E₁₀` diagram, in the node order
`α₀, α₁, …, α₈, α₋₁`: the `E₈` chain, the affine node `0` attached to `α₈` (node `8`), and the
hyperbolic node `9` attached to the affine node. -/
def e10Edge : Fin 9 → Fin 10 × Fin 10 :=
  ![(0,8),(0,9),(1,3),(2,4),(3,4),(4,5),(5,6),(6,7),(7,8)]

/-- The adjacency matrix of the `E₁₀` diagram, as the sum of the elementary matrices of its
edges. Symmetric by construction; this is the form in which the quadratic form of the diagram is
manipulated. -/
def e10Adjacency : Matrix (Fin 10) (Fin 10) ℤ :=
  ∑ k, (Matrix.single (e10Edge k).1 (e10Edge k).2 1 +
    Matrix.single (e10Edge k).2 (e10Edge k).1 1)

/-- The Cartan matrix of the `E₁₀` diagram: `2` on the diagonal and `-1` on the edges. -/
def e10Cartan : Matrix (Fin 10) (Fin 10) ℤ := ![
  ![ 2,  0,  0,  0,  0,  0,  0,  0, -1, -1],
  ![ 0,  2,  0, -1,  0,  0,  0,  0,  0,  0],
  ![ 0,  0,  2,  0, -1,  0,  0,  0,  0,  0],
  ![ 0, -1,  0,  2, -1,  0,  0,  0,  0,  0],
  ![ 0,  0, -1, -1,  2, -1,  0,  0,  0,  0],
  ![ 0,  0,  0,  0, -1,  2, -1,  0,  0,  0],
  ![ 0,  0,  0,  0,  0, -1,  2, -1,  0,  0],
  ![ 0,  0,  0,  0,  0,  0, -1,  2, -1,  0],
  ![-1,  0,  0,  0,  0,  0,  0, -1,  2,  0],
  ![-1,  0,  0,  0,  0,  0,  0,  0,  0,  2]]

set_option maxHeartbeats 1000000 in
/-- The Cartan matrix is `2 · 1` minus the adjacency matrix: the energy form of the diagram. -/
theorem e10Cartan_eq :
    e10Cartan = 2 • (1 : Matrix (Fin 10) (Fin 10) ℤ) - e10Adjacency := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- An integral inverse for the `E₁₀` Cartan matrix. -/
def e10CartanInverse : Matrix (Fin 10) (Fin 10) ℤ := ![
  ![ -2,  -4,  -6,  -8, -12, -10,  -8,  -6,  -4,  -1],
  ![ -4,  -4,  -7,  -9, -14, -12, -10,  -8,  -6,  -2],
  ![ -6,  -7, -10, -14, -21, -18, -15, -12,  -9,  -3],
  ![ -8,  -9, -14, -18, -28, -24, -20, -16, -12,  -4],
  ![-12, -14, -21, -28, -42, -36, -30, -24, -18,  -6],
  ![-10, -12, -18, -24, -36, -30, -25, -20, -15,  -5],
  ![ -8, -10, -15, -20, -30, -25, -20, -16, -12,  -4],
  ![ -6,  -8, -12, -16, -24, -20, -16, -12,  -9,  -3],
  ![ -4,  -6,  -9, -12, -18, -15, -12,  -9,  -6,  -2],
  ![ -1,  -2,  -3,  -4,  -6,  -5,  -4,  -3,  -2,   0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The displayed integral matrix is a right inverse of the `E₁₀` Cartan matrix. -/
theorem e10Cartan_mul_inverse : e10Cartan * e10CartanInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e10Cartan, e10CartanInverse, Matrix.mul_apply, Fin.sum_univ_succ] <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The displayed integral matrix is a left inverse of the `E₁₀` Cartan matrix. -/
theorem e10Cartan_inverse_mul : e10CartanInverse * e10Cartan = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e10Cartan, e10CartanInverse, Matrix.mul_apply, Fin.sum_univ_succ] <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The `E₁₀` Cartan matrix is symmetric. -/
theorem e10Cartan_isSymm : e10Cartan.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ## The quadratic form of the diagram -/

/-- The quadratic form of a `ℤ`-vector in the simple-root coordinates of `E₁₀`:
`b ⬝ᵥ (C b)`. A root of `E₁₀(2)` has `quadC b = 2`. -/
def quadC (b : Fin 10 → ℤ) : ℤ := b ⬝ᵥ (e10Cartan *ᵥ b)

/-- Pairing with the adjacency matrix is twice the edge sum. -/
theorem dotProduct_adjacency (b : Fin 10 → ℤ) :
    b ⬝ᵥ (e10Adjacency *ᵥ b) = 2 * ∑ k, b (e10Edge k).1 * b (e10Edge k).2 := by
  simp only [e10Adjacency, Matrix.sum_mulVec, add_mulVec, Matrix.single_mulVec_eq,
    dotProduct_sum, dotProduct_add, dotProduct_smul, dotProduct_single_one, smul_eq_mul,
    one_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The quadratic form of the diagram in energy form: twice the length minus twice the sum over
the edges. -/
theorem quadC_energy (b : Fin 10 → ℤ) :
    quadC b = 2 * ((∑ i, b i ^ 2) - ∑ k, b (e10Edge k).1 * b (e10Edge k).2) := by
  rw [quadC, e10Cartan_eq, sub_mulVec, dotProduct_sub, smul_mulVec, Matrix.one_mulVec,
    two_smul, dotProduct_adjacency, dotProduct]
  simp only [Pi.add_apply, pow_two, Finset.mul_sum]
  ring

/-- The quadratic form of the diagram is even: it is twice an integer. -/
theorem quadC_even (b : Fin 10 → ℤ) : 2 ∣ quadC b :=
  ⟨_, quadC_energy b⟩

/-! ## `E₁₀(2) = 2 · (U ⊥ E₈)` -/

/-- The Gram matrix of `E₁₀(2)` in the block basis `(e, f, u₀, …, u₇)`: the doubled hyperbolic
plane `U` orthogonally summed with the doubled negative `E₈` root lattice. -/
noncomputable def e10BlockGram : Matrix (Fin 2 ⊕ Fin 8) (Fin 2 ⊕ Fin 8) ℤ :=
  Matrix.fromBlocks (2 • hyperbolicPlaneGramMatrix) 0 0 (2 • e8GramMatrix)

theorem e10BlockGram_isSymm : e10BlockGram.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [e10BlockGram, Matrix.fromBlocks, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, Matrix.zero_apply, hyperbolicPlaneGramMatrix, e8GramMatrix_isSymm.eq] <;>
    decide +revert

/-- `E₁₀(2)`, the doubled even unimodular lattice of signature `(1,9)`. -/
noncomputable def e10Lattice : IntegralLatticeCat ℤ := by
  refine ⟨BilinModuleCat.ofBilinMap (Matrix.toBilin' e10BlockGram), ?_, ?_⟩
  · change Module.Projective ℤ (Fin 2 ⊕ Fin 8 → ℤ)
    infer_instance
  · intro x y
    exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr e10BlockGram_isSymm).eq x y

/-- `E₁₀(2)` as a finite projective lattice. -/
noncomputable def e10FiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ := by
  refine ⟨e10Lattice, ?_⟩
  change Module.Finite ℤ (Fin 2 ⊕ Fin 8 → ℤ)
  infer_instance

@[simp]
theorem e10Lattice_pairing (x y : e10Lattice.obj.carrier) :
    e10Lattice.obj.pairing x y = Matrix.toBilin' e10BlockGram x y :=
  rfl

/-- The block basis has the block Gram matrix. -/
theorem e10Lattice_gramMatrix :
    gramMatrix e10Lattice (Pi.basisFun ℤ (Fin 2 ⊕ Fin 8)) = e10BlockGram :=
  LinearMap.BilinForm.toMatrix'_toBilin' e10BlockGram

/-- Every entry of the Gram matrix is even: `E₁₀(2)` is an even lattice. -/
theorem e10BlockGram_even (i j : Fin 2 ⊕ Fin 8) : 2 ∣ e10BlockGram i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [e10BlockGram, Matrix.fromBlocks, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply,
      Matrix.zero_apply, hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The determinant of the Gram matrix of `E₁₀(2)` is `-2¹⁰`, computed from the block
decomposition: `det (2·U) = 4·(-1)` and `det (2·E₈) = 2⁸·1`. -/
theorem e10BlockGram_det : e10BlockGram.det = -1024 := by
  rw [e10BlockGram, e8GramMatrix_eq, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul,
    Matrix.det_smul, Matrix.det_fin_two]
  norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The signature of `E₁₀(2)` is `(1,9,0)`: computed from the block decomposition, the doubled
hyperbolic plane contributing `(1,1,0)` and the doubled `E₈` contributing `(0,8,0)`. -/
theorem e10BlockGram_signature :
    matrixSignature ℝ (e10BlockGram.map (Int.castRingHom ℝ)) = (1, 9, 0) := by
  have hmap : e10BlockGram.map (Int.castRingHom ℝ) =
      matrixBlockSum ((2 : ℝ) • (hyperbolicPlaneGramMatrix.map (Int.castRingHom ℝ)))
        ((2 : ℝ) • (e8GramMatrix.map (Int.castRingHom ℝ))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [e10BlockGram, matrixBlockSum, Matrix.map_apply, Matrix.fromBlocks,
        Sum.elim_inl, Sum.elim_inr, Matrix.of_apply, Matrix.zero_apply, Matrix.smul_apply,
        hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Int.cast_ofNat, Int.cast_neg] <;>
      norm_num
  rw [hmap, matrixSignature_blockSum, matrixSignature_smul_pos _ (by norm_num : (0:ℝ) < 2),
    matrixSignature_smul_pos _ (by norm_num : (0:ℝ) < 2), hyperbolicPlane_matrixSignature,
    e8Lattice_matrixSignature]
  norm_num

/-- The integral signature of `E₁₀(2)` is `(1,9,0)`, so it has signature `(1,9)`. -/
theorem e10Lattice_integralSignature : integralSignature e10FiniteLattice = (1, 9, 0) := by
  rw [integralSignature_eq_matrixSignature e10FiniteLattice (Pi.basisFun ℤ (Fin 2 ⊕ Fin 8)),
    e10Lattice_gramMatrix]
  exact e10BlockGram_signature

/-! ## The ten simple roots of `E₁₀` inside `E₁₀(2)` -/

/-- The `U`-coordinate of each simple root in the block basis `(e, f)`. -/
def e10RootE : Fin 10 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, -1]

/-- The `f`-coordinate of each simple root in the block basis `(e, f)`. -/
def e10RootF : Fin 10 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The `E₈`-coordinates of each simple root: `α₀ = e - θ` with `θ` the highest root of `E₈`,
the eight simple roots, and `α₋₁ = f - e`. -/
def e10RootW : Fin 10 → Fin 8 → ℤ := ![
  ![-2, -3, -4, -6, -5, -4, -3, -2],
  ![ 1,  0,  0,  0,  0,  0,  0,  0],
  ![ 0,  1,  0,  0,  0,  0,  0,  0],
  ![ 0,  0,  1,  0,  0,  0,  0,  0],
  ![ 0,  0,  0,  1,  0,  0,  0,  0],
  ![ 0,  0,  0,  0,  1,  0,  0,  0],
  ![ 0,  0,  0,  0,  0,  1,  0,  0],
  ![ 0,  0,  0,  0,  0,  0,  1,  0],
  ![ 0,  0,  0,  0,  0,  0,  0,  1],
  ![ 0,  0,  0,  0,  0,  0,  0,  0]]

/-- The ten simple roots of the `E₁₀` diagram as vectors of `E₁₀(2)` in the block basis. -/
def e10Root (i : Fin 10) : Fin 2 ⊕ Fin 8 → ℤ :=
  Sum.elim (fun c => if c = 0 then e10RootE i else e10RootF i) (fun j => e10RootW i j)

/-- The coordinate matrix of the ten simple roots: column `i` is the root `i`. -/
def e10RootMatrix : Matrix (Fin 2 ⊕ Fin 8) (Fin 10) ℤ :=
  fun c i => e10Root i c

/-- The inverse of the coordinate matrix of the simple roots; its column `c` gives the
coordinates of the block basis vector `c` in the simple-root basis (`e = α₀ + θ`,
`f = e + α₋₁`). -/
def e10RootMatrixInverse : Matrix (Fin 10) (Fin 2 ⊕ Fin 8) ℤ :=
  fun i c => ![![1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
              ![2, 2, 1, 0, 0, 0, 0, 0, 0, 0],
              ![3, 3, 0, 1, 0, 0, 0, 0, 0, 0],
              ![4, 4, 0, 0, 1, 0, 0, 0, 0, 0],
              ![6, 6, 0, 0, 0, 1, 0, 0, 0, 0],
              ![5, 5, 0, 0, 0, 0, 1, 0, 0, 0],
              ![4, 4, 0, 0, 0, 0, 0, 1, 0, 0],
              ![3, 3, 0, 0, 0, 0, 0, 0, 1, 0],
              ![2, 2, 0, 0, 0, 0, 0, 0, 0, 1],
              ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]] i c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The coordinate matrix of the simple roots is inverted by `e10RootMatrixInverse`. -/
theorem e10RootMatrix_mul_inverse : e10RootMatrix * e10RootMatrixInverse = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [e10RootMatrix, e10RootMatrixInverse, e10Root, e10RootE, e10RootF, e10RootW,
      Fin.sum_univ_succ, Matrix.mul_apply, Sum.elim_inl, Sum.elim_inr, Matrix.one_apply,
      Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Sum.inl.injEq, Sum.inr.injEq] <;>
    decide

/-! ## The simple roots are a `ℤ`-basis with Gram matrix `-2 · C` -/

/-- The lattice pairing of two simple roots is `-2` times the Cartan matrix: the roots of
`E₁₀(2)` have square `-4` and pair by `2` along the edges. -/
theorem e10Root_pairing (i j : Fin 10) :
    e10Lattice.obj.pairing (e10Root i) (e10Root j) = -2 * e10Cartan i j := by
  rw [e10Lattice_pairing, e8GramMatrix_eq]
  simp only [Matrix.toBilin'_apply', e10BlockGram, e10Root, e10RootE, e10RootF, e10RootW,
    e10Cartan, Matrix.fromBlocks, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.of_apply, Matrix.zero_apply, hyperbolicPlaneGramMatrix,
    Fintype.sum_sum_type, Fin.sum_univ_succ, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec,
    dotProduct, Fin.isValue, Matrix.cons_val, Matrix.empty_val', Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ]

/-! ## The criterion: same-sign coordinates certify the third field -/

section Criterion

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- The image in the real form of a `ℤ`-linear combination of lattice vectors. -/
theorem toRealForm_sum {n : ℕ} (b : Fin n → ℤ) (R : Fin n → L.obj.obj.carrier) :
    toRealForm L (∑ i, b i • R i) = ∑ i, (b i : ℝ) • toRealForm L (R i) := by
  simp only [toRealForm, TensorProduct.tmul_sum, TensorProduct.tmul_smul, Int.cast_smul_eq_zsmul]

/-- **A same-sign combination pairs strictly one way with the interior cone**: if `s` is a
`ℤ`-combination of the roots whose coordinates all have one sign and `s ≠ 0`, then no point of the
interior cone pairs to zero with it. This is the third field of `IsChamberWithWalls` for a root
set whose every reflective root is a same-sign combination of it. -/
theorem pairing_ne_zero_of_signs {t : (realForm L).obj.carrier} {n : ℕ}
    {R : Fin n → L.obj.obj.carrier} {z : (realForm L).obj.carrier}
    (hz : z ∈ rootInteriorCone L t (Set.range R)) {s : L.obj.obj.carrier}
    (b : Fin n → ℤ) (hs : s = ∑ i, b i • R i) (hne : s ≠ 0)
    (hsign : (∀ i, 0 ≤ b i) ∨ ∀ i, b i ≤ 0) :
    (realForm L).obj.pairing z (toRealForm L s) ≠ 0 := by
  have hpos : ∀ i, 0 < (realForm L).obj.pairing z (toRealForm L (R i)) := fun i =>
    (mem_rootInteriorCone_iff L t).mp hz |>.2 (R i) ⟨i, rfl⟩
  have hsome : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by rw [hs]; simp [h])
  rw [hs, toRealForm_sum]
  rcases hsign with h | h
  · obtain ⟨i₀, hi₀⟩ := hsome
    have : 0 < ∑ i, b i * (realForm L).obj.pairing z (toRealForm L (R i)) := by
      apply Finset.sum_pos'
      · intro i _
        exact mul_nonneg (by exact_mod_cast h i) (le_of_lt (hpos i))
      · exact ⟨i₀, Finset.mem_univ _, mul_pos (by exact_mod_cast lt_of_le_of_ne (h i₀) hi₀.symm) (hpos i₀)⟩
    intro hzero
    rw [map_sum] at hzero
    simp only [map_smul, smul_eq_mul] at hzero
    linarith
  · obtain ⟨i₀, hi₀⟩ := hsome
    have : ∑ i, b i * (realForm L).obj.pairing z (toRealForm L (R i)) < 0 := by
      apply Finset.sum_neg'
      · intro i _
        exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h i) (le_of_lt (hpos i))
      · exact ⟨i₀, Finset.mem_univ _, mul_neg_of_neg_of_pos
          (by exact_mod_cast lt_of_le_of_ne (h i₀) (Ne.symm hi₀)) (hpos i₀)⟩
    intro hzero
    rw [map_sum] at hzero
    simp only [map_smul, smul_eq_mul] at hzero
    linarith

/-- **The criterion.** Let `R` be a finite family of negative reflective roots whose interior cone
is nonempty, and suppose every negative reflective root of the lattice is a `ℤ`-combination of `R`
all of whose coordinates have the same sign. Then `C(R)` is a chamber with walls `R`. -/
theorem isChamberWithWalls_of_signs {t : (realForm L).obj.carrier} {n : ℕ}
    (R : Fin n → L.obj.obj.carrier)
    (hroot : ∀ i, R i ∈ negativeReflectiveRoots L)
    (hint : (rootInteriorCone L t (Set.range R)).Nonempty)
    (hsign : ∀ s ∈ negativeReflectiveRoots L, ∃ b : Fin n → ℤ,
      s = ∑ i, b i • R i ∧ ((∀ i, 0 ≤ b i) ∨ ∀ i, b i ≤ 0)) :
    IsChamberWithWalls L t (Set.range R) where
  roots_mem := by
    rintro s ⟨i, rfl⟩
    exact hroot i
  interior_nonempty := hint
  interior_regular := by
    rintro z hz
    refine (mem_weylRegularLocus_iff L t).mpr ⟨hz.1, ?_⟩
    intro s hs hpair
    obtain ⟨b, hb, hsignb⟩ := hsign s hs
    have hne : s ≠ 0 := by
      intro h0
      rw [h0] at hs
      exact absurd hs.2 (lt_irrefl 0)
    exact pairing_ne_zero_of_signs (L := L) hz b hb hne hsignb hpair

end Criterion

/-! ## The interior point and the chamber of `E₁₀(2)` -/

/-- A lattice vector pairing `2` with every simple root of `E₁₀(2)` and having square `2480`: the
sum of the dual basis vectors, doubled. So the interior cone of the root set is nonempty. -/
def e10InteriorPoint : Fin 2 ⊕ Fin 8 → ℤ :=
  Sum.elim ![31, 30] ![-46, -68, -91, -135, -110, -84, -57, -29]

end LeanCategories.Lattices.Valued
