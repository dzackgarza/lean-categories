/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.HigherUnits
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# p-adic logarithm extension data

Definition-level realization of Neukirch FC09-C02-U062.

For a p-adic number field, Neukirch first uses the principal-unit series

`log(1 + z) = z - z^2/2 + z^3/3 - ...`.

After choosing a uniformizer `π`, the multiplicative decomposition from the
preceding proposition supplies a normalized valuation and a principal-unit
component `⟨α⟩`.  Writing `e` for the ramification index and `p` for the
distinguished rational prime, the source then defines

`log π = -(1/e) log ⟨p⟩`

and

`log α = v(α) log π + log ⟨α⟩`.

Sweep III records exactly these formulas.  Summability and continuity of the
principal-unit series, the multiplicative-decomposition identities, the fact
that the resulting map is a homomorphism, `log p = 0`, uniqueness, and
independence of the chosen uniformizer are all result-layer statements.
-/

@[expose] public noncomputable section

open ValuativeRel
open scoped ValuativeRel WithZero

namespace LeanCategories.Algebra

universe u

variable
  (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Principal units of the valuation ring of a local field, using the
definition-level higher-unit carrier already realized in FC09-C02-U041. -/
abbrev LocalPrincipalUnitData : Type u :=
  {u : 𝒪[K]ˣ // u ∈ localPrincipalUnitSet (R := 𝒪[K])}

/-- The alternating p-adic logarithm series at `1 + z`.

The `n = 0` summand is definitionally zero because division by zero in a
field is zero, so this is the source series indexed over all naturals without
an auxiliary shifted index.  Convergence on the principal-unit domain is
result content. -/
def padicLogOnePlusSeriesData (z : K) : K :=
  ∑' n : ℕ, (-1 : K) ^ (n + 1) * z ^ n / (n : K)

/-- The principal-unit logarithm obtained by substituting `u - 1` into the
alternating series.  Its summability and group-homomorphism properties are
not part of the Sweep-III declaration. -/
def principalUnitLogSeriesData (u : LocalPrincipalUnitData K) : K :=
  padicLogOnePlusSeriesData K (((u.1 : 𝒪[K]) : K) - 1)

/-- The normalized additive valuation attached to the canonical value group
of a nonarchimedean local field.

Mathlib's multiplicative convention sends a uniformizer to `exp (-1)`;
negating `WithZero.log` gives Neukirch's convention `v(π) = 1`. -/
def localNormalizedValuationData (x : Kˣ) : ℤ :=
  -WithZero.log
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (x : K)))

/-- The decomposition data from Neukirch Proposition 5.3 needed by the
logarithm construction.

The source's existence and uniqueness of these components are proposition
content.  U062 only consumes the chosen uniformizer, ramification index,
distinguished rational-prime unit, and principal-unit component. -/
structure PadicLogDecompositionData where
  /-- The chosen prime element `π`. -/
  uniformizer : Kˣ
  /-- The ramification index `e` occurring in `p O_K = m^e`. -/
  ramificationIndex : ℕ
  /-- The distinguished rational prime `p`, viewed as a nonzero element of
  the p-adic number field. -/
  basePrime : Kˣ
  /-- The principal-unit component `⟨α⟩` from the multiplicative
  decomposition relative to the chosen uniformizer. -/
  principalUnitPart : Kˣ → LocalPrincipalUnitData K

/-- Neukirch's definition
`log π = -(1/e) log ⟨p⟩` from FC09-C02-U062.

The value is total even before the later theorem `e > 0`; the source
ramification-index facts belong to the result layer. -/
def padicLogUniformizerData (D : PadicLogDecompositionData K) : K :=
  -((D.ramificationIndex : K)⁻¹ *
    principalUnitLogSeriesData K (D.principalUnitPart D.basePrime))

/-- Neukirch's extension formula
`log α = v(α) log π + log ⟨α⟩` from FC09-C02-U062.

This is deliberately an ordinary function rather than a bundled homomorphism:
continuity, multiplicativity, normalization at the rational prime, uniqueness,
and independence of the chosen uniformizer are exactly the propositions
proved after the construction in the source. -/
def padicLogExtensionData
    (D : PadicLogDecompositionData K) (α : Kˣ) : K :=
  (localNormalizedValuationData K α : K) * padicLogUniformizerData K D +
    principalUnitLogSeriesData K (D.principalUnitPart α)

end LeanCategories.Algebra
