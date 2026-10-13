/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Koszul exterior differential data

Definition-level realization of Matsumura FC13-CC-U013.

For a linear functional `φ : M →ₗ[R] R`, the degree-`p` Koszul
differential on the exterior powers is the signed contraction

`d(x₀ ∧ ⋯ ∧ xₚ) = ∑ i, (-1)^i φ(xᵢ)
  (x₀ ∧ ⋯ ∧ x̂ᵢ ∧ ⋯ ∧ xₚ)`.

For a sequence `c : Fin n → R`, Matsumura takes `M = R^n` and the
functional whose value on the `i`th standard basis vector is `c i`.
The definitions below record exactly these graded carriers and contraction
maps.

The skew-Leibniz law, uniqueness of the skew derivation, and `d² = 0` are
proposition/result clauses.  In particular this file deliberately does not
bundle the data into a `ChainComplex`, whose constructor would require the
square-zero theorem.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Algebra

universe u v

variable {R : Type u} [CommRing R] {M : Type v}
  [AddCommGroup M] [Module R M]

/-- The alternating form whose descent to exterior powers is the Koszul
contraction differential associated to `φ`. -/
def koszulExteriorDifferentialAlternating (φ : M →ₗ[R] R) (p : ℕ) :
    M [⋀^Fin (p + 1)]→ₗ[R] ⋀[R]^p M :=
  AlternatingMap.alternatizeUncurryFin
    (φ.smulRight (exteriorPower.ιMulti R p))

/-- Degree-`p` contraction
`Λ^(p+1) M → Λ^p M` associated to a linear functional `φ`. -/
def koszulExteriorDifferential (φ : M →ₗ[R] R) (p : ℕ) :
    ⋀[R]^(p + 1) M →ₗ[R] ⋀[R]^p M :=
  exteriorPower.alternatingMapLinearEquiv
    (koszulExteriorDifferentialAlternating φ p)

/-- For `c₀,…,cₙ₋₁`, the functional on the free module `R^n` sending the
`i`th standard basis vector to `c i`. -/
def koszulSequenceFunctional {n : ℕ} (c : Fin n → R) :
    (Fin n → R) →ₗ[R] R :=
  Fintype.linearCombination R c

/-- Matsumura's degree-`p` Koszul differential for the sequence `c`: the
contraction on `Λ^(p+1)(R^n)` determined by `d(e_i)=c_i`. -/
def koszulSequenceExteriorDifferential {n : ℕ} (c : Fin n → R) (p : ℕ) :
    ⋀[R]^(p + 1) (Fin n → R) →ₗ[R] ⋀[R]^p (Fin n → R) :=
  koszulExteriorDifferential (koszulSequenceFunctional c) p

end LeanCategories.Algebra
