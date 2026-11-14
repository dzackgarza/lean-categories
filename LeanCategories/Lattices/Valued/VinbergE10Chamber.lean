/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.VinbergE10Roots
public import LeanCategories.Lattices.Valued.WeylChambers
public import LeanCategories.Lattices.Valued.Standard
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Vinberg chamber of `E₁₀(2)`

`E₁₀ = U ⊥ E₈` is the even unimodular lattice `II_{1,9}` of signature `(1,9)`; `E₁₀(2)` is the
same `ℤ`-module with the form doubled (the named-lattice catalogue,
`site/catalogues/sage-preamble-definition-catalogue.md`, entries `E10 = U ⊕ E8` and `E10(2)`).
This file builds `E₁₀(2)` from that block definition, exhibits the ten simple roots of the
`E₁₀` diagram inside it as a `ℤ`-basis of the lattice, verifies the three fields of
`IsChamberWithWalls` for that root set — the chamber of `W(E₁₀(2))` — and computes the Coxeter
diagram of the ten roots.
It is the worked instance of `#23` and the consumer of the sign lemma of
`VinbergE10Roots.lean`.

## The data and what is computed

* `e10BlockGram` is the Gram matrix of `E₁₀(2) = 2 · (U ⊥ E₈)` in the block basis
  `(e, f, u₀, …, u₇)`. From it the determinant `-2¹⁰` (`e10BlockGram_det`), the signature
  `(1,9,0)` (`e10BlockGram_signature`, `e10Lattice_integralSignature`) and evenness
  (`e10BlockGram_even`) are computed, not assumed.
* `e10Lattice`, `e10FiniteLattice`: `E₁₀(2)` as an integral and as a finite projective lattice.
* `e10Root i`: the ten simple roots of the `E₁₀` diagram in the node order `α₀, α₁, …, α₈, α₋₁`
  (node `0` the affine node of `E₉ = E₁₀ ∖ {α₋₁}`, nodes `1 … 8` the `E₈` simple roots in the
  order of `e8GramMatrix`, node `9` the hyperbolic extension). `e10RootMatrix_mul_inverse`
  inverts their coordinate matrix, so every vector of the lattice is a `ℤ`-combination of them
  (`e10Root_sum_coord`), and `e10Root_pairing_bilin` computes their Gram matrix as
  `-2 · e10Cartan`: the roots have square `-4` and pair by `2` along the nine edges. Each is a
  negative reflective root of the lattice (`e10SimpleRoot_isReflectiveRoot`,
  `e10SimpleRoot_negSquare`).
* `e10InteriorPoint` is a lattice vector pairing `2` with every simple root and having square
  `2480` (`e10InteriorPoint_pairing`, `e10InteriorPoint_square`), so the interior cone of the
  root set is nonempty (`e10_interior_nonempty`).

## Step 2: the norm of a reflective root

`e10_reflective_norm`: a vector `v = Σ bᵢ αᵢ` of the lattice whose reflection is integral and
whose square is negative has `b ⬝ᵥ (C b) = 2`, hence square `-4` — every reflective vector of
negative square is a root. The route: with `n = b ⬝ᵥ (C b)` one has `(v,v) = -2n` and `n > 0`,
and `n` is even. For each `j`, `e10DualVector j` is the lattice vector with `(α_k, y_j) = 2 δ_kj`,
whose simple-root coordinates are `-C⁻¹ e_j` and are integral because `C` is unimodular
(`e10Cartan_inverse_mul`); `e10Root_pairing_coord` computes `(v, y_j) = 2 b_j`. Integrality of the
reflection at `y_j` then gives `-2n = (v,v) ∣ 2(v, y_j) = 4 b_j`, so `n ∣ 2 b_j`: writing
`2 b_j = n c_j`, `n • c = 2 • b`, hence `n² · quadC c = quadC (2 • b) = 4n` and `n · quadC c = 4`.
So `n ∣ 4`, and `quadC c` is even, so `n ∣ 2`; with `n` even and positive that is `n = 2`. No
Bézout argument and no primitivity of `b` is needed.

## The criterion and the assembly

`isChamberWithWalls_of_signs` is the general criterion for **any** integral lattice `L` of
signature `(1,n)` and any finite root family `R` whose interior cone is nonempty: if every
negative reflective root of `L` is a `ℤ`-combination of `R` whose coordinates all have the same
sign, then `C(R)` is a chamber with walls `R`. Its third field is the observation that a
same-sign combination pairs strictly one way with every point of the interior cone
(`pairing_ne_zero_of_signs`), which needs only that `toRealForm` is `ℤ`-linear
(`toRealForm_sum`).

`e10_isChamberWithWalls` assembles it for `E₁₀(2)`: the sign hypothesis is `e10_reflective_norm`
composed with `quadC_eq_two_signs` of `VinbergE10Roots.lean`, the nonemptiness is the interior
point, and the roots are reflective by evenness of the lattice. The sheet is a parameter — the
statement holds for every `t` on the sheet through the interior point.

## The diagram

`e10CoxeterDiagram` is `coxeterDiagramOfRoots` of the ten simple roots. Its edge weight is the
normalized pairing square `(αᵢ, αⱼ)² / ((αᵢ)² (αⱼ)²) = C_ij² / 4`, since the roots have square
`-4` and pair by `-2 C_ij`: weight `1` on the diagonal, `1/4` on each of the nine edges of the
`E₁₀` diagram and `0` on orthogonal pairs, so the diagram's support is exactly the off-diagonal
support of the Cartan matrix (`e10CoxeterDiagram_edges`, `e10CoxeterDiagram_edges_zero_iff`,
`e10CoxeterDiagram_edges_self`, `e10CoxeterDiagram_edges_edge`).

## References

* È. B. Vinberg, *The groups of unit elements of certain quadratic forms*, Mat. Sb. 87 (1972),
  §1 (the chambers of the reflection group of a lattice in the positive cone) and §3.2
  (Propositions 4 and 5: the algorithm and the completeness of a wall set).
* V. G. Kac, *Infinite-dimensional Lie algebras*, 3rd ed., Prop. 5.1 and §5.1: the real roots of
  a symmetrizable Kac–Moody algebra are the `W`-translates of the simple roots.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.3: the
  finite-type argument that every root is a nonnegative integral combination of the simple ones,
  the statement `quadC_eq_two_signs` extends to the hyperbolic diagram `E₁₀`.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1, for the notion of a chamber and its walls
  (`WeylChambers.lean`).

## LC-09 record

Searched (the formalization corpus, and the Mathlib source at the pinned head):
`content:IsCoxeter`, `content:fundamental domain reflection`,
`content:hyperbolic polyhedron finite volume`, `content:Vinberg`, `content:IsChamberWithWalls`,
`content:PosSemidef submatrix`, `content:Matrix.PosDef.submatrix`, `content:CartanMatrix E8`,
`content:Vinberg chamber Lorentzian root system`, `file:LinearAlgebra/RootSystem/Chamber`, plus
local greps over `Mathlib/` for `IsReflective`, `IsCoxeter`, `fundamentalDomain`, `chamber`,
`PosSemidef`, `CartanMatrix`, `matrixSignature`, `finSumFinEquiv`. Hits in Mathlib:
`CartanMatrix.E₆`, `E₇`, `E₈` with `E₆_off_diag_nonpos` and `isSimplyLaced_E₆`
(`Mathlib/LinearAlgebra/Matrix/Cartan.lean`) — Mathlib carries the Cartan matrices of the
*finite* types only, has no `E₁₀` and no `IsFiniteCartan`, so the Cartan form is stated here
directly; `CoxeterMatrix` (`Mathlib/GroupTheory/Coxeter/Matrix.lean:69`, combinatorial, no
geometric chamber); `MeasureTheory/Group/FundamentalDomain` (measurable, not polyhedral);
`Matrix.PosSemidef.submatrix` (`Mathlib/LinearAlgebra/Matrix/PosDef.lean:80`). Nothing supplies
positive *semi*definiteness for a diagram of affine or indefinite type, a null-vector statement,
or the norm characterization of a reflective root, so the sum-of-squares certificates of
`VinbergE10Roots.lean` and the argument of this file are proved directly; nothing is ported.
-/

@[expose] public section



open Matrix
open QuadraticMap
open LeanCategories.Algebra
open LeanCategories.Modules.Bilinear.Valued
open scoped BigOperators

namespace LeanCategories.Lattices.Valued

/-! ## `E₁₀(2) = 2 · (U ⊥ E₈)` -/

/-- The Gram matrix of `E₁₀(2)` in the block basis `(e, f, u₀, …, u₇)`: the doubled hyperbolic
plane `U` orthogonally summed with the doubled negative `E₈` root lattice. The scalar of the two
blocks is `(2 : ℤ)`, so that `Matrix.det_smul` and `matrixSignature_smul_pos` apply to them
without a cast step. -/
noncomputable def e10BlockGram : Matrix (Fin 2 ⊕ Fin 8) (Fin 2 ⊕ Fin 8) ℤ :=
  Matrix.fromBlocks ((2 : ℤ) • hyperbolicPlaneGramMatrix) 0 0 ((2 : ℤ) • e8GramMatrix)

/-- The hyperbolic-plane block of the Gram matrix, entrywise. -/
theorem e10BlockGram_inl_inl (a b : Fin 2) :
    e10BlockGram (Sum.inl a) (Sum.inl b) = 2 * hyperbolicPlaneGramMatrix a b := by
  rw [e10BlockGram, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, smul_eq_mul]

/-- The off-diagonal block of the Gram matrix is zero. -/
theorem e10BlockGram_inl_inr (a : Fin 2) (b : Fin 8) :
    e10BlockGram (Sum.inl a) (Sum.inr b) = 0 := by
  rw [e10BlockGram, Matrix.fromBlocks_apply₁₂]
  rfl

/-- The off-diagonal block of the Gram matrix is zero. -/
theorem e10BlockGram_inr_inl (a : Fin 8) (b : Fin 2) :
    e10BlockGram (Sum.inr a) (Sum.inl b) = 0 := by
  rw [e10BlockGram, Matrix.fromBlocks_apply₂₁]
  rfl

/-- The `E₈` block of the Gram matrix, entrywise. -/
theorem e10BlockGram_inr_inr (a b : Fin 8) :
    e10BlockGram (Sum.inr a) (Sum.inr b) = 2 * e8GramMatrix a b := by
  rw [e10BlockGram, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]

/-- The Gram matrix is symmetric: it is a block diagonal matrix of two symmetric blocks. -/
theorem e10BlockGram_isSymm : e10BlockGram.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · simp only [e10BlockGram_inl_inl, hyperbolicPlaneGramMatrix_isSymm.apply]
  · simp only [e10BlockGram_inr_inl, e10BlockGram_inl_inr]
  · simp only [e10BlockGram_inl_inr, e10BlockGram_inr_inl]
  · simp only [e10BlockGram_inr_inr, e8GramMatrix_isSymm.apply]

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
  rcases i with i | i <;> rcases j with j | j
  · simp only [e10BlockGram_inl_inl]
    exact ⟨_, rfl⟩
  · simp only [e10BlockGram_inl_inr, dvd_zero]
  · simp only [e10BlockGram_inr_inl, dvd_zero]
  · simp only [e10BlockGram_inr_inr]
    exact ⟨_, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- the `10 × 10` determinant of the block Gram matrix is expanded entrywise
/-- The determinant of the Gram matrix of `E₁₀(2)` is `-2¹⁰`, computed from the block
decomposition: `det (2·U) = 4·(-1)` and `det (2·E₈) = 2⁸·1`. -/
theorem e10BlockGram_det : e10BlockGram.det = -1024 := by
  have h1 : ((2 : ℤ) • hyperbolicPlaneGramMatrix).det = -4 := by
    rw [Matrix.det_smul, Matrix.det_fin_two]
    norm_num [hyperbolicPlaneGramMatrix]
  have h2 : ((2 : ℤ) • e8GramMatrix).det = 256 := by
    rw [Matrix.det_smul, e8GramMatrix_det]
    norm_num
  rw [e10BlockGram, Matrix.det_fromBlocks_zero₁₂, h1, h2]
  norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- the signature of the doubled `E₈` block is read off its `8 × 8` literal
/-- The signature of `E₁₀(2)` is `(1,9,0)`: computed from the block decomposition, the doubled
hyperbolic plane contributing `(1,1,0)` and the doubled `E₈` contributing `(0,8,0)`. -/
theorem e10BlockGram_signature :
    matrixSignature ℝ (e10BlockGram.map (Int.castRingHom ℝ)) = (1, 9, 0) := by
  have hmap : e10BlockGram.map (Int.castRingHom ℝ) =
      matrixBlockSum ((2 : ℝ) • (hyperbolicPlaneGramMatrix.map (Int.castRingHom ℝ)))
        ((2 : ℝ) • (e8GramMatrix.map (Int.castRingHom ℝ))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [matrixBlockSum, Matrix.fromBlocks_apply₁₁, Matrix.map_apply,
        e10BlockGram_inl_inl, Matrix.smul_apply, map_mul, smul_eq_mul]
      norm_num
    · simp only [matrixBlockSum, Matrix.fromBlocks_apply₁₂, Matrix.map_apply,
        e10BlockGram_inl_inr, Matrix.map_apply, Matrix.zero_apply, map_zero]
    · simp only [matrixBlockSum, Matrix.fromBlocks_apply₂₁, Matrix.map_apply,
        e10BlockGram_inr_inl, Matrix.map_apply, Matrix.zero_apply, map_zero]
    · simp only [matrixBlockSum, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
        e10BlockGram_inr_inr, Matrix.smul_apply, map_mul, smul_eq_mul]
      norm_num
  rw [hmap, matrixSignature_blockSum, matrixSignature_smul_pos _ (by norm_num : (0:ℝ) < 2),
    matrixSignature_smul_pos _ (by norm_num : (0:ℝ) < 2), hyperbolicPlane_matrixSignature,
    e8Lattice_matrixSignature]
  norm_num

/-- The integral signature of `E₁₀(2)` is `(1,9,0)`, so it has signature `(1,9)`. -/
theorem e10Lattice_integralSignature : integralSignature e10FiniteLattice = (1, 9, 0) := by
  let b : Module.Basis (Fin 2 ⊕ Fin 8) ℤ e10FiniteLattice.obj.obj.carrier :=
    Pi.basisFun ℤ (Fin 2 ⊕ Fin 8)
  rw [integralSignature_eq_matrixSignature e10FiniteLattice b]
  have hb : gramMatrix e10FiniteLattice.obj b = e10BlockGram := e10Lattice_gramMatrix
  rw [hb]
  exact e10BlockGram_signature

/-- The positive index of `E₁₀(2)` is one. -/
theorem e10Lattice_integralSignature_pos : (integralSignature e10FiniteLattice).1 = 1 := by
  rw [e10Lattice_integralSignature]

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

/-- The ten simple roots of the `E₁₀` diagram as block vectors of `E₁₀(2)`. -/
def e10Root (i : Fin 10) : Fin 2 ⊕ Fin 8 → ℤ :=
  Sum.elim (fun c => if c = 0 then e10RootE i else e10RootF i) (fun j => e10RootW i j)

/-- The coordinate matrix of the ten simple roots: column `i` is the root `i`. -/
def e10RootMatrix : Matrix (Fin 2 ⊕ Fin 8) (Fin 10) ℤ :=
  fun c i => e10Root i c

/-- The inverse of the coordinate matrix of the simple roots: column `c` gives the coordinates
of the block basis vector `c` in the simple-root basis (`e = α₀ + θ`, `f = e + α₋₁`, and the
`E₈` basis vector `uⱼ` is `α_{j+1}`). -/
def e10RootMatrixInverse : Matrix (Fin 10) (Fin 2 ⊕ Fin 8) ℤ :=
  fun i c => Sum.elim (fun u =>
    ![![1, 1], ![2, 2], ![3, 3], ![4, 4], ![6, 6], ![5, 5], ![4, 4], ![3, 3], ![2, 2],
      ![0, 1]] i u) (fun j => if i = Fin.succ (Fin.castSucc j) then (1 : ℤ) else 0) c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- the hundred entries of the product are decided one by one
/-- The coordinate matrix of the simple roots is inverted by `e10RootMatrixInverse`. -/
theorem e10RootMatrix_mul_inverse : e10RootMatrix * e10RootMatrixInverse = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp only [e10RootMatrix, e10RootMatrixInverse, e10Root, e10RootE, e10RootF, e10RootW,
      Fin.sum_univ_succ, Matrix.mul_apply, Sum.elim_inl, Sum.elim_inr, Matrix.one_apply,
      Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero] <;>
    decide

/-! ## The simple roots span the lattice and pair by `-2 · C` -/

set_option maxHeartbeats 2000000 in
-- the hundred entry pairs of the Cartan form are expanded by `norm_num`
/-- The lattice pairing of two simple roots is `-2` times the Cartan matrix: the roots of
`E₁₀(2)` have square `-4` and pair by `2` along the edges. -/
theorem e10Root_pairing_bilin (i j : Fin 10) :
    Matrix.toBilin' e10BlockGram (e10Root i) (e10Root j) = -2 * e10Cartan i j := by
  rw [Matrix.toBilin'_apply]
  simp only [Fintype.sum_sum_type, e10Root, e10RootE, e10RootF, e10RootW, e10Cartan,
    Sum.elim_inl, Sum.elim_inr, e10BlockGram_inl_inl, e10BlockGram_inl_inr,
    e10BlockGram_inr_inl, e10BlockGram_inr_inr, hyperbolicPlaneGramMatrix, e8GramMatrix_eq,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.of_apply, mul_zero,
    zero_mul, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ]

/-- The ten simple roots as vectors of the lattice `E₁₀(2)`. -/
def e10SimpleRoot (i : Fin 10) : e10FiniteLattice.obj.obj.carrier := e10Root i

/-- The pairing of two simple roots of the lattice. -/
theorem e10SimpleRoot_pairing (i j : Fin 10) :
    e10FiniteLattice.obj.obj.pairing (e10SimpleRoot i) (e10SimpleRoot j) =
      -2 * e10Cartan i j :=
  e10Root_pairing_bilin i j


/-! ## Simple-root coordinates -/

/-- The coordinates of a block vector in the simple-root basis: the integral matrix
`e10RootMatrixInverse` applied to `v`. -/
def e10RootCoord (v : Fin 2 ⊕ Fin 8 → ℤ) : Fin 10 → ℤ := e10RootMatrixInverse *ᵥ v

/-- Every block vector is the sum of its simple-root coordinates times the simple roots. -/
theorem e10Root_sum_coord (v : Fin 2 ⊕ Fin 8 → ℤ) :
    ∑ i, e10RootCoord v i • e10Root i = v := by
  have hmat : (∑ i, e10RootCoord v i • e10Root i) = e10RootMatrix *ᵥ e10RootCoord v := by
    funext c
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, e10RootMatrix]
    ring
  rw [hmat, e10RootCoord, Matrix.mulVec_mulVec, e10RootMatrix_mul_inverse, Matrix.one_mulVec]

/-- Every vector of the lattice is the sum of its simple-root coordinates times the simple
roots. -/
theorem e10Root_sum_coord_carrier (v : e10FiniteLattice.obj.obj.carrier) :
    ∑ i, e10RootCoord v i • e10SimpleRoot i = v :=
  e10Root_sum_coord v

/-- **The pairing of two simple-root combinations.** Both arguments expanded in the simple-root
basis: the form of `E₁₀(2)` on the simple roots is `-2 C`, so the pairing of two combinations is
`-2 (b ⬝ᵥ (C c))`. -/
theorem e10Root_sum_pairing (b c : Fin 10 → ℤ) :
    Matrix.toBilin' e10BlockGram (∑ i, b i • e10Root i) (∑ j, c j • e10Root j)
      = -2 * (b ⬝ᵥ (e10Cartan *ᵥ c)) := by
  have h1 : ∀ y : Fin 2 ⊕ Fin 8 → ℤ,
      Matrix.toBilin' e10BlockGram (∑ i, b i • e10Root i) y
        = ∑ i, b i * Matrix.toBilin' e10BlockGram (e10Root i) y := by
    intro y
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h2 : ∀ i : Fin 10,
      Matrix.toBilin' e10BlockGram (e10Root i) (∑ j, c j • e10Root j)
        = ∑ j, c j * Matrix.toBilin' e10BlockGram (e10Root i) (e10Root j) := by
    intro i
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, smul_eq_mul]
  simp only [h1, h2, e10Root_pairing_bilin]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## The dual vectors of the simple roots -/

/-- The simple-root coordinates of the vector dual to `α_j`: `-C⁻¹ e_j`. -/
def e10DualCoord (j : Fin 10) : Fin 10 → ℤ := fun k => -(e10CartanInverse k j)

/-- The lattice vector dual to the simple root `α_j`: the vector `y_j` with `(α_k, y_j) = 2 δ_kj`
— twice the Kronecker delta, because the simple roots of `E₁₀(2)` have square `-4`. Its
simple-root coordinates are `-C⁻¹ e_j`, integral because `C` is unimodular
(`e10Cartan_mul_inverse`). -/
def e10DualVector (j : Fin 10) : Fin 2 ⊕ Fin 8 → ℤ :=
  ∑ k, e10DualCoord j k • e10Root k

/-- The Cartan matrix carries the dual coordinate vector `-C⁻¹ e_j` to `-e_j`. -/
theorem e10Cartan_mulVec_dualCoord (i j : Fin 10) :
    (e10Cartan *ᵥ e10DualCoord j) i = -(if i = j then 1 else 0) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [e10DualCoord, mul_neg]
  rw [Finset.sum_neg_distrib, ← Matrix.mul_apply, e10Cartan_mul_inverse, Matrix.one_apply]

/-- The pairing of a simple root with the dual vector of `α_j` is `2 δ_ij`. -/
theorem e10Root_pairing_dual (i j : Fin 10) :
    Matrix.toBilin' e10BlockGram (e10Root i) (e10DualVector j)
      = 2 * (if i = j then 1 else 0) := by
  have hsingle : (∑ k, (Pi.single i (1 : ℤ) : Fin 10 → ℤ) k • e10Root k) = e10Root i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hdot : ((Pi.single i (1 : ℤ) : Fin 10 → ℤ) ⬝ᵥ (e10Cartan *ᵥ e10DualCoord j))
      = (e10Cartan *ᵥ e10DualCoord j) i := by
    rw [dotProduct]
    refine Eq.trans (Finset.sum_eq_single i ?_ ?_) ?_
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · intro h
      exact absurd (Finset.mem_univ i) h
    · simp
  rw [← hsingle, show e10DualVector j = ∑ k, e10DualCoord j k • e10Root k from rfl,
    e10Root_sum_pairing, hdot, e10Cartan_mulVec_dualCoord]
  by_cases h : i = j <;> simp [h]

/-- **The pairing with a dual vector is twice a coordinate**: for every block vector `v` and
simple root `α_j`, the pairing with the dual vector `y_j` is `2 b_j`, where `b = e10RootCoord v`
are the simple-root coordinates of `v`. -/
theorem e10Root_pairing_coord (v : Fin 2 ⊕ Fin 8 → ℤ) (j : Fin 10) :
    Matrix.toBilin' e10BlockGram v (e10DualVector j) = 2 * e10RootCoord v j := by
  conv_lhs => rw [← e10Root_sum_coord v]
  rw [show e10DualVector j = ∑ k, e10DualCoord j k • e10Root k from rfl, e10Root_sum_pairing]
  have hdot : (e10RootCoord v ⬝ᵥ (e10Cartan *ᵥ e10DualCoord j)) = - e10RootCoord v j := by
    rw [dotProduct]
    have hstep : ∀ i : Fin 10,
        e10RootCoord v i * (e10Cartan *ᵥ e10DualCoord j) i
          = -(e10RootCoord v i * (if i = j then 1 else 0)) := by
      intro i
      rw [e10Cartan_mulVec_dualCoord, mul_neg]
    simp only [hstep, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [hdot]
  ring

/-! ## Step 2: a negative reflective root has `quadC`-value `2` -/

set_option maxHeartbeats 800000 in
-- the quadratic-form bookkeeping runs over all ten coordinates
/-- **The norm characterization of the reflective roots of `E₁₀(2)`.** If a vector
`v = Σ bᵢ αᵢ` of the lattice is reflective of negative square, then `b ⬝ᵥ (C b) = 2`, i.e.
`(v, v) = -4`: a vector of `E₁₀(2)` whose reflection is integral and whose square is negative
has square `-4` exactly, so it is a root of the reflection group.

Let `n = quadC b`, so that `(v, v) = -2n` and `n > 0`, and `n` is even (`quadC_even`). For each
`j`, the dual vector `y_j` has `(α_i, y_j) = 2 δ_ij`; reflectivity at `y_j` gives
`-2n = (v,v) ∣ 2(v, y_j) = 4 b_j`, so `n ∣ 2 b_j`. Write `2 b_j = n c_j`. Then `n • c = 2 • b`, so
`n² · quadC c = quadC (n • c) = quadC (2 • b) = 4n`, and `n · quadC c = 4` since `n ≠ 0`. Hence
`n ∣ 4`; `quadC c` is even, so `n ∣ 2`, and with `n` even and positive that is `n = 2`. -/
theorem e10_reflective_norm (v : Fin 2 ⊕ Fin 8 → ℤ)
    (hv : LinearMap.IsReflective (Matrix.toBilin' e10BlockGram) v)
    (hneg : Matrix.toBilin' e10BlockGram v v < 0) :
    quadC (e10RootCoord v) = 2 := by
  set b : Fin 10 → ℤ := e10RootCoord v with hb
  set n : ℤ := quadC b with hn
  have hnn : Matrix.toBilin' e10BlockGram v v = -2 * n := by
    rw [← e10Root_sum_coord v, e10Root_sum_pairing, ← hb, hn]
    rfl
  have hnpos : 0 < n := by rw [hnn] at hneg; linarith
  have hdvd : ∀ j : Fin 10, n ∣ 2 * b j := by
    intro j
    obtain ⟨k, hk⟩ := hv.dvd_two_mul (e10DualVector j)
    have h2 : Matrix.toBilin' e10BlockGram v (e10DualVector j) = 2 * b j :=
      e10Root_pairing_coord v j
    rw [hnn, h2] at hk
    exact ⟨-k, by linarith⟩
  choose c hc using hdvd
  have hnc : n • c = (2 : ℤ) • b := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith [hc j]
  have hquad : n ^ 2 * quadC c = 4 * n := by
    have h1 : quadC (n • c) = quadC ((2 : ℤ) • b) := by rw [hnc]
    rw [quadC_smul, quadC_smul, ← hn] at h1
    norm_num at h1 ⊢
    exact h1
  have hnQ : n * quadC c = 4 := by
    have h0 : n * (n * quadC c - 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (ne_of_gt hnpos)
    · exact sub_eq_zero.mp h
  obtain ⟨m, hm⟩ := quadC_even c
  have hnm : n * m = 2 := by
    have h : n * (2 * m) = 4 := by rw [← hm]; exact hnQ
    linarith
  obtain ⟨t, ht⟩ := quadC_even b
  have htm : t * m = 1 := by
    rw [← hn] at ht
    nlinarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one htm with h | h
  · rw [hn, ht, h]
    norm_num
  · rw [hn, ht, h] at hnpos
    norm_num at hnpos


/-! ## The lattice pairing of `E₁₀(2)` is even and the simple roots are reflective -/

/-- The lattice pairing of `E₁₀(2)` is even: every value of its form is a multiple of `2`. -/
theorem e10Bilin_even (x y : Fin 2 ⊕ Fin 8 → ℤ) :
    2 ∣ Matrix.toBilin' e10BlockGram x y := by
  rw [Matrix.toBilin'_apply]
  refine Finset.dvd_sum fun c _ => Finset.dvd_sum fun c' _ => ?_
  obtain ⟨k, hk⟩ := e10BlockGram_even c c'
  exact ⟨x c * k * y c', by rw [hk]; ring⟩

/-- Every simple root of `E₁₀(2)` has square `-4`, so it is of negative square. -/
theorem e10SimpleRoot_negSquare (i : Fin 10) :
    e10FiniteLattice.obj.obj.pairing (e10SimpleRoot i) (e10SimpleRoot i) < 0 := by
  rw [e10SimpleRoot_pairing]
  have h : e10Cartan i i = 2 := by fin_cases i <;> rfl
  rw [h]
  norm_num

/-- **The simple roots are reflective**: the square of a simple root is `-4`, and `-4` divides
`2 · (αᵢ, y)` for every lattice vector `y` because the lattice is even. -/
theorem e10SimpleRoot_isReflectiveRoot (i : Fin 10) :
    IsReflectiveRoot e10FiniteLattice.obj (e10SimpleRoot i) where
  regular := by
    have h : e10FiniteLattice.obj.obj.bilinMap (e10SimpleRoot i) (e10SimpleRoot i) = -4 := by
      rw [BilinModuleCat.bilinMap_apply, e10SimpleRoot_pairing]
      have h2 : e10Cartan i i = 2 := by fin_cases i <;> rfl
      rw [h2]
      norm_num
    rw [h]
    exact IsRegular.of_ne_zero (by norm_num)
  dvd_two_mul := by
    intro y
    have h : e10FiniteLattice.obj.obj.bilinMap (e10SimpleRoot i) (e10SimpleRoot i) = -4 := by
      rw [BilinModuleCat.bilinMap_apply, e10SimpleRoot_pairing]
      have h2 : e10Cartan i i = 2 := by fin_cases i <;> rfl
      rw [h2]
      norm_num
    obtain ⟨k, hk⟩ := e10Bilin_even (e10Root i) y
    have h2 : e10FiniteLattice.obj.obj.bilinMap (e10SimpleRoot i) y = 2 * k := by
      rw [BilinModuleCat.bilinMap_apply]
      exact hk
    rw [h, h2]
    exact ⟨-k, by ring⟩

/-! ## The interior point of the chamber -/

/-- A lattice vector pairing `2` with every simple root of `E₁₀(2)` and having square `2480`: the
sum of the dual basis vectors, doubled. So the interior cone of the root set is nonempty. -/
def e10InteriorPoint : Fin 2 ⊕ Fin 8 → ℤ :=
  Sum.elim ![31, 30] ![-46, -68, -91, -135, -110, -84, -57, -29]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- the double sum over `Fin 2 ⊕ Fin 8` is expanded entrywise
/-- The interior point pairs `2` with every simple root. -/
theorem e10InteriorPoint_pairing (i : Fin 10) :
    Matrix.toBilin' e10BlockGram e10InteriorPoint (e10Root i) = 2 := by
  rw [Matrix.toBilin'_apply]
  simp only [e10InteriorPoint, e10Root, e10RootE, e10RootF, e10RootW, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, e10BlockGram_inl_inl, e10BlockGram_inl_inr,
    e10BlockGram_inr_inl, e10BlockGram_inr_inr, hyperbolicPlaneGramMatrix, e8GramMatrix_eq,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.of_apply, mul_zero,
    zero_mul, Fin.sum_univ_succ]
  fin_cases i <;> norm_num [Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- the double sum over `Fin 2 ⊕ Fin 8` is expanded entrywise
/-- The interior point has square `2480`, so it lies in the positive cone. -/
theorem e10InteriorPoint_square :
    Matrix.toBilin' e10BlockGram e10InteriorPoint e10InteriorPoint = 2480 := by
  rw [Matrix.toBilin'_apply]
  simp only [e10InteriorPoint, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    e10BlockGram_inl_inl, e10BlockGram_inl_inr, e10BlockGram_inr_inl, e10BlockGram_inr_inr,
    hyperbolicPlaneGramMatrix, e8GramMatrix_eq, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.of_apply, mul_zero, zero_mul, Fin.sum_univ_succ]
  norm_num [Fin.sum_univ_succ]

/-- **The interior cone of the ten simple roots is nonempty**: a point of the sheet through the
interior point pairs strictly positively with every simple root. -/
theorem e10_interior_nonempty {t : (realForm e10FiniteLattice).obj.carrier}
    (ht : toRealForm e10FiniteLattice e10InteriorPoint ∈
      positiveCone.upper (realFormQuadratic e10FiniteLattice) t) :
    (rootInteriorCone e10FiniteLattice t (Set.range e10SimpleRoot)).Nonempty := by
  refine ⟨toRealForm e10FiniteLattice e10InteriorPoint, ht, ?_⟩
  rintro r ⟨i, rfl⟩
  have h := realFormPairing_toRealForm (L := e10FiniteLattice)
    (u := (e10InteriorPoint : e10FiniteLattice.obj.obj.carrier))
    (v := (e10SimpleRoot i : e10FiniteLattice.obj.obj.carrier))
  rw [h]
  change (0 : ℝ) < ((Matrix.toBilin' e10BlockGram e10InteriorPoint (e10Root i) : ℤ) : ℝ)
  rw [e10InteriorPoint_pairing i]
  norm_num

/-! ## The criterion: same-sign coordinates certify the third field -/

section Criterion

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- The pairing of the real form is additive in its second argument. -/
theorem realForm_pairing_sum {ι : Type*} (s : Finset ι)
    (f : ι → (realForm L).obj.carrier) (z : (realForm L).obj.carrier) :
    (realForm L).obj.pairing z (∑ i ∈ s, f i) = ∑ i ∈ s, (realForm L).obj.pairing z (f i) := by
  simp only [← BilinModuleCat.bilinMap_apply, map_sum]

/-- The image in the real form of a sum of lattice vectors is the sum of the images. -/
theorem toRealForm_add (x y : L.obj.obj.carrier) :
    toRealForm L (x + y) = toRealForm L x + toRealForm L y := by
  change (1 : ℝ) ⊗ₜ[ℤ] (x + y) = (1 : ℝ) ⊗ₜ[ℤ] x + (1 : ℝ) ⊗ₜ[ℤ] y
  rw [TensorProduct.tmul_add]

/-- The image in the real form of an integer multiple. -/
theorem toRealForm_zsmul (k : ℤ) (x : L.obj.obj.carrier) :
    toRealForm L (k • x) = (k : ℝ) • toRealForm L x := by
  change (1 : ℝ) ⊗ₜ[ℤ] (k • x) = (k : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] x)
  rw [← Int.cast_smul_eq_zsmul ℤ k x]
  rw [TensorProduct.tmul_smul]
  exact (Int.cast_smul_eq_zsmul ℝ k ((1 : ℝ) ⊗ₜ[ℤ] x)).symm

/-- The image in the real form of a `ℤ`-linear combination of lattice vectors. -/
theorem toRealForm_sum {n : ℕ} (b : Fin n → ℤ) (R : Fin n → L.obj.obj.carrier) :
    toRealForm L (∑ i, b i • R i) = ∑ i, (b i : ℝ) • toRealForm L (R i) := by
  have h : ∀ s : Finset (Fin n), toRealForm L (∑ i ∈ s, b i • R i)
      = ∑ i ∈ s, (b i : ℝ) • toRealForm L (R i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        change (1 : ℝ) ⊗ₜ[ℤ] (0 : L.obj.obj.carrier) = 0
        rw [TensorProduct.tmul_zero]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, toRealForm_add, ih, toRealForm_zsmul]
  simpa using h Finset.univ

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
  have hsplit : (realForm L).obj.pairing z (toRealForm L s)
      = ∑ i, (b i : ℝ) * (realForm L).obj.pairing z (toRealForm L (R i)) := by
    rw [hs, toRealForm_sum, realForm_pairing_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [BilinModuleCat.pairing_smul_right, smul_eq_mul]
  rw [hsplit]
  obtain ⟨i₀, hi₀⟩ := hsome
  rcases hsign with h | h
  · have hlt : 0 < ∑ i, (b i : ℝ) * (realForm L).obj.pairing z (toRealForm L (R i)) := by
      apply Finset.sum_pos'
      · intro i _
        exact mul_nonneg (by exact_mod_cast h i) (le_of_lt (hpos i))
      · exact ⟨i₀, Finset.mem_univ _,
          mul_pos (by exact_mod_cast lt_of_le_of_ne (h i₀) (Ne.symm hi₀)) (hpos i₀)⟩
    exact ne_of_gt hlt
  · have hlt : ∑ i, (b i : ℝ) * (realForm L).obj.pairing z (toRealForm L (R i)) < 0 := by
      apply Finset.sum_neg'
      · intro i _
        exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h i) (le_of_lt (hpos i))
      · exact ⟨i₀, Finset.mem_univ _,
          mul_neg_of_neg_of_pos (by exact_mod_cast lt_of_le_of_ne (h i₀) hi₀) (hpos i₀)⟩
    exact ne_of_lt hlt

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
      simpa using hs.2
    exact pairing_ne_zero_of_signs (L := L) hz b hb hne hsignb hpair

end Criterion

/-! ## The chamber and the diagram of `E₁₀(2)` -/

/-- **The ten simple roots of `E₁₀(2)` cut out a chamber with walls themselves** (#23): the
`E₁₀` chamber of the reflection group `W(E₁₀(2))`. Every negative reflective root of `E₁₀(2)` is
a same-sign `ℤ`-combination of the ten simple roots — its simple-root coordinates `b` satisfy
`b ⬝ᵥ (C b) = 2` (`e10_reflective_norm`), and such a vector has coordinates of one sign
(`quadC_eq_two_signs`) — so the criterion `isChamberWithWalls_of_signs` applies, with the interior
cone spanned by `e10InteriorPoint`.

The sheet is a parameter: the statement holds for every `t` on the sheet through the interior
point, which is what `ht` says. -/
theorem e10_isChamberWithWalls {t : (realForm e10FiniteLattice).obj.carrier}
    (ht : toRealForm e10FiniteLattice e10InteriorPoint ∈
      positiveCone.upper (realFormQuadratic e10FiniteLattice) t) :
    IsChamberWithWalls e10FiniteLattice t (Set.range e10SimpleRoot) := by
  refine isChamberWithWalls_of_signs (L := e10FiniteLattice) e10SimpleRoot ?_ ?_ ?_
  · intro i
    exact ⟨e10SimpleRoot_isReflectiveRoot i, e10SimpleRoot_negSquare i⟩
  · exact e10_interior_nonempty ht
  · intro s hs
    obtain ⟨hrefl, hneg⟩ := hs
    have hnorm : quadC (e10RootCoord s) = 2 := e10_reflective_norm s hrefl hneg
    exact ⟨e10RootCoord s, (e10Root_sum_coord_carrier s).symm, quadC_eq_two_signs _ hnorm⟩

/-- **The Coxeter diagram of the ten simple roots of `E₁₀(2)`** (#23; Vinberg 1972, §1): the edge
weight between `αᵢ` and `αⱼ` is the normalized pairing square
`(αᵢ, αⱼ)² / ((αᵢ)² (αⱼ)²)`. The simple roots have square `-4` and pair by `-2 C_ij`, so the
weight is `C_ij² / 4`: `1` on the diagonal, `1/4` on the nine edges of the `E₁₀` diagram, and `0`
on orthogonal pairs (`e10CoxeterDiagram_edges`, `e10CoxeterDiagram_edges_zero_iff`). -/
noncomputable def e10CoxeterDiagram : CoxeterDiagram (Fin 10) :=
  coxeterDiagramOfRoots e10FiniteLattice e10SimpleRoot e10SimpleRoot_negSquare

/-- The edge weight of the diagram of the ten simple roots: `C_ij²/4`. -/
theorem e10CoxeterDiagram_edges (i j : Fin 10) :
    e10CoxeterDiagram.edges i j = (e10Cartan i j : ℚ) ^ 2 / 4 := by
  change (coxeterDiagramOfRoots e10FiniteLattice e10SimpleRoot e10SimpleRoot_negSquare).edges i j
    = (e10Cartan i j : ℚ) ^ 2 / 4
  rw [coxeterDiagramOfRoots_edges]
  simp only [coxeterDiagramOfRootsEdges]
  rw [e10SimpleRoot_pairing i j, e10SimpleRoot_pairing i i, e10SimpleRoot_pairing j j]
  have hi : e10Cartan i i = 2 := by fin_cases i <;> rfl
  have hj : e10Cartan j j = 2 := by fin_cases j <;> rfl
  rw [hi, hj]
  push_cast
  ring

/-- The diagram has an edge exactly on the off-diagonal nonzeros of the Cartan matrix: the support
of the diagram of the simple roots is the `E₁₀` diagram. -/
theorem e10CoxeterDiagram_edges_zero_iff (i j : Fin 10) :
    e10CoxeterDiagram.edges i j = 0 ↔ e10Cartan i j = 0 := by
  rw [e10CoxeterDiagram_edges]
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h2 | h2
    · have h3 : (e10Cartan i j : ℚ) = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp h2
      exact_mod_cast h3
    · exact absurd h2 h4
  · intro h
    rw [h]
    norm_num

/-- On the diagonal the diagram of the simple roots carries weight `1`. -/
theorem e10CoxeterDiagram_edges_self (i : Fin 10) : e10CoxeterDiagram.edges i i = 1 := by
  rw [e10CoxeterDiagram_edges]
  have hi : e10Cartan i i = 2 := by fin_cases i <;> rfl
  rw [hi]
  norm_num

/-- On each of the nine edges of the `E₁₀` diagram the weight is `1/4`. -/
theorem e10CoxeterDiagram_edges_edge (k : Fin 9) :
    e10CoxeterDiagram.edges (e10Edge k).1 (e10Edge k).2 = 1 / 4 := by
  rw [e10CoxeterDiagram_edges]
  have h : e10Cartan (e10Edge k).1 (e10Edge k).2 = -1 := by
    fin_cases k <;> decide
  rw [h]
  norm_num
end LeanCategories.Lattices.Valued
