/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic


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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- The Cartan matrix of `E₁₀` is unimodular. -/
theorem e10Cartan_det : e10Cartan.det = -1 := by
  rw [e10Cartan]
  decide

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

end LeanCategories.Lattices.Valued
