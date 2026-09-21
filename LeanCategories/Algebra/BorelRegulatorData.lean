/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Borel-regulator source data

Definition-level realization of the construction part of Neukirch
FC09-C07-U015.

The checked libraries do not construct the higher algebraic K-group
`K~_(4k-1)(Z)` or Borel's regulator.  Sweep III therefore takes a rational
model of that source and its regulator map as supplied data.  It records the
regulator representative and its class up to nonzero rational scaling.

Nonvanishing of the regulator, independence of the chosen nonzero K-class,
and the comparison with the odd zeta value are result-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

/-- Source-supplied rational higher-K group and Borel regulator in degree
`4k-1`.  The index `k` records the degree convention from Neukirch. -/
structure BorelRegulatorSourceData (k : ℕ) where
  /-- A model of `K~_(4k-1)(Z) tensor Q`. -/
  source : Type u
  [addCommGroup : AddCommGroup source]
  /-- The supplied Borel regulator map. -/
  regulator : source → ℝ

attribute [instance] BorelRegulatorSourceData.addCommGroup

/-- Nonzero rational rescaling of real regulator representatives. -/
def BorelRationalScaleRelData (x y : ℝ) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ y = (q : ℝ) * x

/-- Raw carrier for real regulator values modulo multiplication by a nonzero
rational number.

Using `Quot` avoids proving relation laws during Sweep III.  On nonzero real
values this is the source quotient `R^* / Q^*`. -/
abbrev BorelRegulatorScaleClassData := Quot BorelRationalScaleRelData

/-- The representative real value of a supplied higher-K class. -/
def borelRegulatorRepresentativeData {k : ℕ}
    (D : BorelRegulatorSourceData k) (x : D.source) : ℝ :=
  D.regulator x

/-- The regulator representative modulo nonzero rational scaling. -/
def borelRegulatorClassData {k : ℕ}
    (D : BorelRegulatorSourceData k) (x : D.source) :
    BorelRegulatorScaleClassData :=
  Quot.mk _ (borelRegulatorRepresentativeData D x)

/-- The source condition on the higher-K representative used to name the
`2k`-th regulator.  It is kept separate from the construction. -/
def IsBorelRegulatorRepresentativeData {k : ℕ}
    (D : BorelRegulatorSourceData k) (x : D.source) : Prop :=
  x ≠ 0

end LeanCategories.Algebra
