/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.KoszulDeviationPort

/-!
# Koszul deviations

Definition-level realization of Matsumura, *Commutative Ring Theory*, §21,
pp. 169--171 (`FC13-C07-U046`, `FC13-C07-U049`).

For a Noetherian local ring `A`, Matsumura chooses a minimal generating
system `x` of the maximal ideal and defines

  `ε_p(A) = dim_k H_p(x; A)`,  `k = A / m`.

The imported PR #34913 port constructs such a minimal generating list
canonically from `Submodule.FG.finite_generators`, builds its Koszul complex,
proves that the maximal ideal annihilates every homology group, and thereby
constructs the residue-field module structure needed for `finrank`.

Thus `koszulDeviation A p` is an actual construction from `A` and `p`;
no generator system, homology module, comparison isomorphism, candidate, or
choice fallback is supplied by callers.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace LeanCategories.Algebra

universe u

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Matsumura's Koszul deviation
`ε_p(A) = dim_{A/m} H_p(x;A)` for the canonical minimal generator list `x`
of the maximal ideal. -/
def koszulDeviation (p : ℕ) : ℕ :=
  Module.finrank (ResidueField A) ((matsumuraKoszulAlgebraData A).homology p)

/-- Matsumura's definition of a complete-intersection local ring:
`ε₁(A) + dim A = embdim A`. -/
def IsCompleteIntersectionLocalRingData : Prop :=
  (koszulDeviation A 1 : WithBot ℕ∞) + ringKrullDim A =
    ((maximalIdeal A).spanFinrank : WithBot ℕ∞)

end LeanCategories.Algebra
