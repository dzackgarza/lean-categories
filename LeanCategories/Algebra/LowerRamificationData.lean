/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Lower ramification filtration data

Definition-level realization of Neukirch FC09-C02-U125.

For a discrete additive valuation with values in `WithTop ℤ`, the inequality
`v(σa-a) ≥ s+1` for a real index `s` is equivalent to the integer inequality
`v(σa-a) ≥ ⌈s+1⌉`.  The source domain is `s ≥ -1`; the raw formula below is
defined for every real `s` and can be restricted by consumers without putting
a proof into the index type.

Sweep III records only the membership locus.  Subgroup closure, normality,
antitonicity, and the identifications of the initial terms are result content.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Raw lower ramification locus at real index `s` for a chosen Galois subgroup.

The condition `0 ≤ v a` is the additive-valuation form of `a` lying in the
valuation ring. -/
def lowerRamificationSet (v : AddValuation L (WithTop ℤ))
    (G : Subgroup (L ≃ₐ[K] L)) (s : ℝ) : Set G :=
  {σ | ∀ a : L, (0 : WithTop ℤ) ≤ v a →
    ((⌈s + 1⌉ : ℤ) : WithTop ℤ) ≤ v (σ.1 a - a)}

end LeanCategories.Algebra
