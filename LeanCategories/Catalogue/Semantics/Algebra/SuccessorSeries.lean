/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Series
public import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Catalogue

@[expose] public section

/-!
# The summable family `(n+1)t^n`

This new family is an infinite function with domain `ℕ`. Its summability,
admission, sum and coefficient use the existing owners. The positive value is
proved for the entire family; no finite sample stands in for its binder input.
The constant-one family is a separating case excluded by actual summability.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.SuccessorSeries

open Series
attribute [local instance] Series.tAdic

/-- For the selected commutative ring `R`, the set map `ℕ → PowerSeries R`
sending every index `n` to `PowerSeries.C (n + 1 : R) * PowerSeries.X ^ n`.
Its `n`th term has coefficient `(n + 1 : R)` at degree `n` and zero at every
other degree, with the natural coefficient cast into this actual ring.
This is the complete infinite family, with no truncation parameter.
`successorTerms_summable` proves summability in the selected `(X)`-adic
topology `powerSeriesTAdic R`; `successorTerms_admission` retains the same
function, and `successorTerms_sum` gives the sum with coefficient `n + 1`
at every degree `n`. -/
noncomputable def successorTerms (R : CommRingCat.{0}) :
    (ℕ : Type) ⟶ CasCatalogue.Algebra.Calculus.powerSeries R :=
  TypeCat.ofHom fun n => PowerSeries.C (n + 1 : R) * PowerSeries.X ^ n

/-- Each term is divisible by its corresponding power of `t`. -/
theorem successorTerms_summable (R : CommRingCat.{0}) :
    Summable (fun n : ℕ => successorTerms R n) :=
  summable_of_X_pow_dvd fun _ => dvd_mul_left _ _

/-- Admission keeps the very same infinite function. -/
theorem successorTerms_admission (R : CommRingCat.{0}) :
    ((Series.admit (powerSeriesTAdic R) ℕ (fun n => successorTerms R n)
      (successorTerms_summable R)) 0).toFun = (fun n => successorTerms R n) := rfl

/-- The old power-series binder sums this new family to its full coefficient function. -/
theorem successorTerms_sum (R : CommRingCat.{0}) :
    powerSeriesSum R ℕ ⟨(fun n => successorTerms R n), successorTerms_summable R⟩ =
      PowerSeries.mk (fun n => (n + 1 : R)) :=
  powerSeriesSum_C_mul_X_pow R (fun n => (n + 1 : R)) (successorTerms_summable R)

/-- The fixed integer degree-three observation is four, not the square-family value nine. -/
theorem integer_degree_three :
    PowerSeries.coeff 3 (powerSeriesSum NamedCommutativeRings.integers ℕ
      ⟨(fun n => successorTerms NamedCommutativeRings.integers n),
        successorTerms_summable NamedCommutativeRings.integers⟩) = (4 : ℤ) := by
  rw [successorTerms_sum, PowerSeries.coeff_mk]
  norm_num

/-- The constant-one family cannot be admitted in the selected `(t)`-adic topology. -/
theorem integer_constant_one_not_summable :
    ¬ Summable (fun _ : ℕ => (1 : PowerSeries ℤ)) := by
  intro h
  have hc := (Series.hasSum_iff_hasSum_coeff.mp h.hasSum) 0
  letI : TopologicalSpace ℤ := ⊥
  haveI : DiscreteTopology ℤ := ⟨rfl⟩
  have hs : Summable (fun _ : ℕ => (1 : ℤ)) := by
    simpa using hc.summable
  have hz : (1 : ℤ) = 0 := (summable_const_iff (1 : ℤ)).mp hs
  norm_num at hz

/-- No object in the existing admission domain can have this nonsummable function. -/
theorem no_constant_one_admission :
    ¬ ∃ F : SummableFamily (powerSeriesTAdic NamedCommutativeRings.integers) ℕ,
      F.toFun = (fun _ : ℕ => (1 : PowerSeries ℤ)) := by
  rintro ⟨F, hF⟩
  exact integer_constant_one_not_summable (hF ▸ F.summable)

end CasCatalogue.Algebra.SuccessorSeries

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.sets.successor_power_series_terms"⟩, category := CategoryId.sets
    name := "successor_power_series_terms"
    declaration := `CasCatalogue.Algebra.SuccessorSeries.successorTerms }

end CasCatalogue
