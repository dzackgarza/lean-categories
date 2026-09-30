/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# The Hessian at a singular point of a homogeneous polynomial

Let `F ∈ k[x_σ]` be homogeneous of degree `n` and let `p` be a point at which every first
partial derivative of `F` vanishes. Euler's identity for the homogeneous polynomial `∂_j F`
of degree `n - 1` reads `∑ i, x_i ∂_i ∂_j F = (n - 1) ∂_j F`; evaluating at `p` gives
`p ᵥ* H(F)(p) = 0`. Over a field, a nonzero such `p` therefore forces
`rank H(F)(p) ≤ |σ| - 1`.

Provenance: migrated from `dzackgarza/research`, `formalization/coble-enriques/NodeCriteria.lean`
(`hessian_rank_le_two_of_singular`, stated for three variables and a point on the curve). That
statement is the instance `σ = Fin 3`, recovered as `hessianAt_rank_le_two_of_singular`. The
general version drops the hypothesis `F(p) = 0`, which the proof never uses (and which follows
from the vanishing of the partials by Euler's identity when `n` is invertible).

LC-09 search: the formalization corpus returns nothing for "Hessian homogeneous polynomial
singular point Euler"; Mathlib supplies Euler's identity
(`MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`) and homogeneity of partials
(`MvPolynomial.IsHomogeneous.pderiv`) and no Hessian matrix.
-/

namespace LeanCategories.AlgebraicGeometry

open MvPolynomial Matrix

variable {σ : Type*} {k : Type*}

/-- The Hessian matrix of `F` evaluated at `p`: entry `(i, j)` is `(∂_i ∂_j F)(p)`. -/
noncomputable def hessianAt [CommSemiring k] (F : MvPolynomial σ k) (p : σ → k) :
    Matrix σ σ k :=
  Matrix.of fun i j ↦ eval p (pderiv i (pderiv j F))

/-- `p` is a singular point of `F` when `F(p) = 0` and every first partial vanishes at `p`. -/
def IsSingularPoint [CommSemiring k] (F : MvPolynomial σ k) (p : σ → k) : Prop :=
  eval p F = 0 ∧ ∀ j, eval p (pderiv j F) = 0

variable [Fintype σ]

/-- If every first partial of a homogeneous `F` vanishes at `p`, then `p` is in the left kernel
of the Hessian at `p`. -/
theorem vecMul_hessianAt_eq_zero [CommRing k] {F : MvPolynomial σ k} {n : ℕ} {p : σ → k}
    (hF : F.IsHomogeneous n) (hp : ∀ j, eval p (pderiv j F) = 0) :
    p ᵥ* hessianAt F p = 0 := by
  ext j
  have h := congr_arg (eval p) (hF.pderiv (i := j)).sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, map_nsmul, hp j, nsmul_zero] at h
  simpa [Matrix.vecMul, dotProduct, hessianAt] using h

/-- Over a field, the Hessian of a homogeneous polynomial at a nonzero point where every first
partial vanishes has rank at most `|σ| - 1`. -/
theorem hessianAt_rank_le_of_pderiv_eq_zero [Field k] {F : MvPolynomial σ k} {n : ℕ}
    {p : σ → k} (hF : F.IsHomogeneous n) (hp : ∀ j, eval p (pderiv j F) = 0) (hp0 : p ≠ 0) :
    (hessianAt F p).rank ≤ Fintype.card σ - 1 := by
  classical
  set H := hessianAt F p
  have hker : p ∈ LinearMap.ker (Hᵀ.mulVecLin) := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
    exact vecMul_hessianAt_eq_zero hF hp
  have hpos : 0 < Module.finrank k (LinearMap.ker (Hᵀ.mulVecLin)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨p, hker⟩, fun h ↦ hp0 (congr_arg Subtype.val h)⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (Hᵀ.mulVecLin)
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  rw [← Matrix.rank_transpose, Matrix.rank]
  omega

/-- The rank bound at a nonzero singular point. -/
theorem hessianAt_rank_le_of_isSingularPoint [Field k] {F : MvPolynomial σ k} {n : ℕ}
    {p : σ → k} (hF : F.IsHomogeneous n) (hs : IsSingularPoint F p) (hp0 : p ≠ 0) :
    (hessianAt F p).rank ≤ Fintype.card σ - 1 :=
  hessianAt_rank_le_of_pderiv_eq_zero hF hs.2 hp0

/-- The plane-curve instance: at a nonzero singular point of a homogeneous ternary polynomial,
the `3 × 3` Hessian has rank at most `2` (the node criterion of the Coble corpus). -/
theorem hessianAt_rank_le_two_of_singular [Field k] {F : MvPolynomial (Fin 3) k} {n : ℕ}
    {p : Fin 3 → k} (hF : F.IsHomogeneous n) (hs : IsSingularPoint F p) (hp0 : p ≠ 0) :
    (hessianAt F p).rank ≤ 2 := by
  simpa using hessianAt_rank_le_of_isSingularPoint hF hs hp0

end LeanCategories.AlgebraicGeometry
