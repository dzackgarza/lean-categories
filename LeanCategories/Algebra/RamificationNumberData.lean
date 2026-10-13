/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.LowerRamificationData

/-!
# Ramification-number data

Definition-level realization of Neukirch FC09-C02-U129.

After Lemma 10.4 chooses an integral generator `x` with
`O_L = O_K[x]`, Neukirch defines

`i_{L/K}(σ) = v_L(σ x - x)`.

The source then proves that this value is independent of the chosen generator
and identifies every lower ramification group by the single inequality
`i_{L/K}(σ) ≥ s + 1`.

Sweep III records the chosen-generator function and the corresponding raw
inequality locus only.  Existence of a monogenic generator, independence of
the value from that generator, and comparison with the all-integral-elements
lower filtration are result-layer statements.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe uK uL

variable
  (K : Type uK) {L : Type uL}
  [Field K] [Field L] [Algebra K L]

/-- Neukirch's ramification number evaluated at a chosen monogenic generator:
`i_x(σ) = v_L(σx - x)`.

The parameter `x` is the generator chosen by the preceding monogenicity
lemma.  No proof of monogenicity or generator-independence is required to
form this value. -/
def ramificationNumberAtGeneratorData
    (v : AddValuation L (WithTop ℤ))
    (x : L) (σ : L ≃ₐ[K] L) : WithTop ℤ :=
  v (σ x - x)

/-- The raw lower-ramification locus expressed using the chosen-generator
ramification number:
`{σ | i_x(σ) ≥ s+1}`.

Because the valuation is integer-valued, the real-index inequality is written
with `⌈s+1⌉`, matching the existing FC09-C02-U125 owner.  Equality with
`lowerRamificationSet` is result content. -/
def ramificationNumberLowerSetData
    (v : AddValuation L (WithTop ℤ))
    (G : Subgroup (L ≃ₐ[K] L))
    (x : L) (s : ℝ) : Set G :=
  {σ |
    ((⌈s + 1⌉ : ℤ) : WithTop ℤ) ≤
      ramificationNumberAtGeneratorData K v x σ.1}

end LeanCategories.Algebra
