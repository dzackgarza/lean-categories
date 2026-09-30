/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Elementary calculus (SPEC.md, "Elementary calculus")

Each operation of calculus is a total map out of the object it is defined on (LC-14):
* `sin`, `cos`, `exp : ℝ → ℝ` and `π : 1 → ℝ` (Mathlib `Real.sin`, `Real.cos`, `Real.exp`,
  `Real.pi`);
* `C(ℝ)`, the continuous maps `ℝ → ℝ` (Mathlib `ContinuousMap`), and the definite integral
  `∫_a^b f` of `f ∈ C(ℝ)`, `ℝ × ℝ → ℝ` (Mathlib `intervalIntegral`; continuous maps are
  integrable on every interval). A map is in `C(ℝ)` only with the evidence that it is continuous;
* `C^∞(ℝ)`, the smooth maps `ℝ → ℝ` (Mathlib `ContDiff ℝ ⊤`), and the Taylor expansion
  `C^∞(ℝ) × ℝ → ℝ[[t]]`, `(f, a) ↦ Σ f⁽ᵏ⁾(a)/k! tᵏ` (Mathlib `iteratedDeriv`). A map is in
  `C^∞(ℝ)` only with the evidence that it is smooth;
* `R[[t]]` (Mathlib `PowerSeries`), refined by the ring `R[[t]]`, with its variable, constants, its
  coefficients `R[[t]] × ℕ → R`, and the series with a given coefficient sequence
  `(ℕ → R) → R[[t]]`, `c ↦ Σ c(n) tⁿ` (Mathlib `PowerSeries.mk`), which is what `Σ c(n) tⁿ` means;
* `x^n : X × ℕ → X` in a monoid (Mathlib `Monoid.npow`).

Limits are not registered: `lim_{t → a}` is defined on the maps that have a limit at `a`, and no
registered construction places a map there.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.Calculus

open CasCatalogue.Foundation.PowerSets CasCatalogue.Algebra.NumberSystems

/-- `sin : ℝ → ℝ`. -/
noncomputable def sin : reals ⟶ reals := TypeCat.ofHom Real.sin

/-- `cos : ℝ → ℝ`. -/
noncomputable def cos : reals ⟶ reals := TypeCat.ofHom Real.cos

/-- `exp : ℝ → ℝ`. -/
noncomputable def exp : reals ⟶ reals := TypeCat.ofHom Real.exp

/-- `π ∈ ℝ`. -/
noncomputable def pi : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals :=
  TypeCat.ofHom fun _ => Real.pi

/-- `C(ℝ)`, the continuous maps `ℝ → ℝ`. -/
abbrev continuousMaps : SetsCat.{0} := C(ℝ, ℝ)

/-- The continuous map `f`, with the evidence that `f` is continuous. -/
def admitContinuous (f : ℝ → ℝ) (h : Continuous f) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ continuousMaps :=
  TypeCat.ofHom fun _ => ⟨f, h⟩

/-- `(f, (a, b)) ↦ ∫_a^b f`. -/
noncomputable def integral :
    (continuousMaps × (reals × reals) : SetsCat.{0}) ⟶ reals :=
  TypeCat.ofHom fun p => ∫ t in p.2.1..p.2.2, p.1 t

/-- `C^∞(ℝ)`, the smooth maps `ℝ → ℝ`. -/
abbrev smoothMaps : SetsCat.{0} := {f : ℝ → ℝ // ContDiff ℝ (⊤ : ℕ∞) f}

/-- The smooth map `f`, with the evidence that `f` is smooth. -/
def admitSmooth (f : ℝ → ℝ) (h : ContDiff ℝ (⊤ : ℕ∞) f) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ smoothMaps :=
  TypeCat.ofHom fun _ => ⟨f, h⟩

/-- `R[[t]]`. -/
abbrev powerSeries (R : Type) [CommRing R] : SetsCat.{0} := PowerSeries R

/-- The variable `t ∈ R[[t]]`. -/
noncomputable def powerSeriesGenerator (R : Type) [CommRing R] :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ powerSeries R :=
  TypeCat.ofHom fun _ => PowerSeries.X

/-- The constants `R ↪ R[[t]]`. -/
noncomputable def powerSeriesConstants (R : Type) [CommRing R] :
    (R : SetsCat.{0}) ⟶ powerSeries R :=
  TypeCat.ofHom fun r => PowerSeries.C r

/-- `R[[t]]` as a ring. -/
noncomputable abbrev ringPowerSeries (R : Type) [CommRing R] : LeanCategories.Algebra.Rings.{0} :=
  RingCat.of (PowerSeries R)

/-- The underlying set of the ring `R[[t]]` is `R[[t]]`. -/
def ringPowerSeriesIdentification (R : Type) [CommRing R] :
    (powerSeries R : SetsCat.{0}) ≅ powerSeries R :=
  Iso.refl _

/-- The coefficient of `tⁿ`. -/
noncomputable def coefficient (R : Type) [CommRing R] :
    (powerSeries R × CasCatalogue.Foundation.Objects.naturals : SetsCat.{0}) ⟶ (R : SetsCat.{0}) :=
  TypeCat.ofHom fun p => PowerSeries.coeff p.2 p.1

/-- `Σ c(n) tⁿ`, the series with the coefficient sequence `c : ℕ → R`. -/
noncomputable def ofCoefficients (R : Type) [CommRing R]
    (c : CasCatalogue.Foundation.Objects.naturals ⟶ (R : SetsCat.{0})) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ powerSeries R :=
  TypeCat.ofHom fun _ => PowerSeries.mk (ConcreteCategory.hom (C := Type) c)

/-- `(x, n) ↦ xⁿ` in a monoid. -/
def power (X : Type) [Monoid X] : (X × CasCatalogue.Foundation.Objects.naturals : SetsCat.{0}) ⟶
    (X : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 ^ p.2

/-- `(f, a) ↦ Σ f⁽ᵏ⁾(a)/k! tᵏ`. -/
noncomputable def taylor :
    (smoothMaps × reals : SetsCat.{0}) ⟶ powerSeries ℝ :=
  TypeCat.ofHom fun p =>
    PowerSeries.mk fun k => iteratedDeriv k p.1.1 p.2 / k.factorial

end CasCatalogue.Algebra.Calculus

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.sets.real_sin"⟩, category := CategoryId.sets, name := "sin"
    declaration := `CasCatalogue.Algebra.Calculus.sin }

normalized_registry .morphism
  { id := ⟨"mor.sets.real_cos"⟩, category := CategoryId.sets, name := "cos"
    declaration := `CasCatalogue.Algebra.Calculus.cos }

normalized_registry .morphism
  { id := ⟨"mor.sets.real_exp"⟩, category := CategoryId.sets, name := "exp"
    declaration := `CasCatalogue.Algebra.Calculus.exp }

normalized_registry .morphism
  { id := ⟨"mor.sets.real_pi"⟩, category := CategoryId.sets, name := "π"
    declaration := `CasCatalogue.Algebra.Calculus.pi }

normalized_registry .object
  { id := ⟨"obj.sets.continuous_maps"⟩, category := CategoryId.sets, name := "C"
    declaration := `CasCatalogue.Algebra.Calculus.continuousMaps
    admission := some `CasCatalogue.Algebra.Calculus.admitContinuous }

normalized_registry .morphism
  { id := ⟨"mor.sets.real_integral"⟩, category := CategoryId.sets, name := "∫ₐᵇ"
    declaration := `CasCatalogue.Algebra.Calculus.integral }

normalized_registry .object
  { id := ⟨"obj.sets.smooth_maps"⟩, category := CategoryId.sets, name := "C^∞"
    declaration := `CasCatalogue.Algebra.Calculus.smoothMaps
    admission := some `CasCatalogue.Algebra.Calculus.admitSmooth }

normalized_registry .object
  { id := ⟨"obj.sets.power_series"⟩, category := CategoryId.sets, name := "PowerSeries"
    declaration := `CasCatalogue.Algebra.Calculus.powerSeries
    generator := some `CasCatalogue.Algebra.Calculus.powerSeriesGenerator
    constants := some `CasCatalogue.Algebra.Calculus.powerSeriesConstants }

normalized_registry .object
  { id := ⟨"obj.rings.power_series"⟩, category := CategoryId.rings, name := "PowerSeries"
    declaration := `CasCatalogue.Algebra.Calculus.ringPowerSeries
    refines := some
      { base := ⟨"obj.sets.power_series"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.Calculus.ringPowerSeriesIdentification } }

normalized_registry .morphism
  { id := ⟨"mor.sets.power_series_coefficient"⟩, category := CategoryId.sets, name := "coefficient"
    declaration := `CasCatalogue.Algebra.Calculus.coefficient }

normalized_registry .morphism
  { id := ⟨"mor.sets.power_series_of_coefficients"⟩, category := CategoryId.sets
    name := "Σ tⁿ"
    declaration := `CasCatalogue.Algebra.Calculus.ofCoefficients }

normalized_registry .morphism
  { id := ⟨"mor.sets.monoid_power"⟩, category := CategoryId.sets, name := "^"
    declaration := `CasCatalogue.Algebra.Calculus.power }

normalized_registry .morphism
  { id := ⟨"mor.sets.taylor_expansion"⟩, category := CategoryId.sets, name := "taylor_expansion"
    declaration := `CasCatalogue.Algebra.Calculus.taylor }

end CasCatalogue
