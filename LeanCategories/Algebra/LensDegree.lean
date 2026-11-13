module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

open scoped BigOperators

/-!
# The local-degree bookkeeping for the angular extension of `S^{2n-1}`

Card `E-HAT-3.E-2` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.E, exercise 2 (the lens-space discussion).  Certificate:
new-qual-site `proofs/cards/LensDegree.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): `det_angDeriv` (corpus: 0 hits).  Route: written — the arithmetic
bookkeeping is the card's settled proof.

# `E-HAT-3.E-2`: the local-degree bookkeeping for the angular extension of `S^{2n-1}`

The map `f~` of the exercise is the *angular* extension: it fixes the radii and multiplies the
`j`-th angular coordinate by `k_j`. In the oriented frame `(∂_r, r⁻¹∂_θ)` of the punctured plane
the `j`-th coordinate map has derivative `diag(1, k_j)`, so its local degree there is the sign of
`k_j`; there are `|k_j|` preimages, and the contribution of the coordinate is
`|k_j| · sgn(k_j) = k_j`, whose product over the coordinates is `k_1 ⋯ k_n`.

What this file certifies is *arithmetic only*: that the linear map `diag(1, k)` of the frame has
determinant `k`, that it preserves orientation exactly when `k > 0`, and that `|k| sgn(k) = k` holds
per coordinate and multiplies over a finite set of coordinates.

It does **not** certify, and should not be read as certifying, any of the geometric steps:

* that the angular extension `f~` has derivative `diag(1, k_j)` in that frame,
* that its local degree at a preimage is therefore `sgn(k_j)`,
* the degree formula `deg f~ = k_1 ⋯ k_n` for self-maps of `S^{2n-1}`, or
* the degree of `f`, which the card gets from the covering square `p' f~ = f p`.

The first three are inputs quoted from the lens-space discussion in §3.E and are named as such in
the card; the last is a consequence of those inputs together with multiplicativity of degree.

It also does not certify the holomorphic comparison: `z ↦ z^k` is conformal on `ℂ^×` for every
`k ≠ 0`, so its local degree is `+1`, and it is *not* the angular extension when `k < 0` (it
moves the radius as well). That distinction is the reason this bookkeeping is about the frame
derivative and not about the complex derivative.
-/

namespace LeanCategories.Algebra.LensDegree

/-- The derivative of the angular extension in one coordinate, in the oriented frame
`(∂_r, r⁻¹∂_θ)`: the radius is untouched and the angular coordinate is multiplied by `k`. -/
def angDeriv (k : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1, k * p.2)
  map_add' p q := by
    ext <;> simp [mul_add]
  map_smul' c p := by
    ext <;> simp [mul_left_comm]

/-- Its matrix in that frame is `diag(1, k)`, and the determinant is `k`. -/
theorem det_angDeriv (k : ℝ) : Matrix.det !![(1 : ℝ), 0; 0, k] = k := by
  rw [Matrix.det_fin_two]
  simp

/-- The coordinate map preserves the orientation exactly when `k > 0`: this is the local degree
`sgn(k)` of the angular extension, read off the determinant. -/
theorem orientation_iff (k : ℝ) :
    0 < Matrix.det !![(1 : ℝ), 0; 0, k] ↔ 0 < k := by
  rw [det_angDeriv]

/-- One coordinate contributes `|k| · sgn(k) = k`: `|k|` preimages, each with local degree
`sgn(k)` read as `1` or `-1`. -/
theorem natAbs_mul_orientation (k : ℤ) :
    (k.natAbs : ℤ) * (if 0 < k then (1 : ℤ) else -1) = k := by
  have h : k = (k.natAbs : ℤ) ∨ k = -(k.natAbs : ℤ) := Int.natAbs_eq k
  split_ifs with hk <;> rcases h with h | h <;> omega

/-- The product over the coordinates: the total degree contribution is the product of the
`k_j`, i.e. the number of preimages times the sign accumulated over the coordinates. -/
theorem prod_natAbs_mul_orientation {ι : Type*} (s : Finset ι) (k : ι → ℤ) :
    ((s.prod fun j => (k j).natAbs : ℕ) : ℤ) * (s.prod fun j => if 0 < k j then (1 : ℤ) else -1)
      = s.prod fun j => k j := by
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => natAbs_mul_orientation (k j)

end LeanCategories.Algebra.LensDegree
