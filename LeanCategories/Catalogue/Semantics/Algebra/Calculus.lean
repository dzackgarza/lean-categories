/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence

@[expose] public section

/-!
# Elementary calculus (SPEC.md, "Elementary calculus")

Each operation of calculus is a total map out of the object it is defined on (LC-14):
* `sin`, `cos`, `exp : ℝ → ℝ` and `π : 1 → ℝ` (Mathlib `Real.sin`, `Real.cos`, `Real.exp`,
  `Real.pi`);
* `C(ℝ)`, the continuous maps `ℝ → ℝ` (Mathlib `ContinuousMap`), and the definite integral
  `∫_a^b : C(ℝ) → ℝ` at bounds `a b ∈ ℝ`, the binder `∫_{a}^{b} e dt` (Mathlib
  `intervalIntegral`; continuous maps are integrable on every interval). A map is in `C(ℝ)` only
  with the evidence that it is continuous;
* `C^∞(ℝ)`, the smooth maps `ℝ → ℝ` (Mathlib `ContDiff ℝ ⊤`), and the Taylor expansion
  `C^∞(ℝ) × ℝ → ℝ[[t]]`, `(f, a) ↦ Σ f⁽ᵏ⁾(a)/k! tᵏ` (Mathlib `iteratedDeriv`). A map is in
  `C^∞(ℝ)` only with the evidence that it is smooth. The division by `k!` is the division
  `ℝ × ℝˣ → ℝ` by a unit (`Algebra.Units`, LC-16): `k!` is the image of `k! ∈ ℕ` under the initial
  map `ℕ → ℝ`, a unit because it is nonzero in the field `ℝ` of characteristic `0`. Its coefficients
  are Mathlib's Taylor coefficients `taylorCoeffWithin f k ℝ a` (`taylor_coeff`);
* `R[[t]]` (Mathlib `PowerSeries`), refined by the ring `R[[t]]`, with its variable, constants, its
  coefficients `R[[t]] × ℕ → R`, and the series with a given coefficient sequence
  `(ℕ → R) → R[[t]]`, `c ↦ Σ c(n) tⁿ` (Mathlib `PowerSeries.mk`), which is what `Σ c(n) tⁿ` means;
* `x^n : X × ℕ → X` in a monoid (Mathlib `Monoid.npow`).

Limits `lim_{t → a}` are defined on the maps that converge at `a` (`Algebra.RealLimits`), series
`∑_{n ∈ N}` on the summable families (`Algebra.Series`).
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

open Lean Elab Tactic in
/-- The evidence that a closed map `f : ℝ → ℝ` is continuous: `f` is built from the identity and
constants by `+`, `-`, `·`, `^ n`, division by a map without zeros, `sin`, `cos`, `exp` and
composition; each of these is continuous (`Real.continuous_sin`, `Real.continuous_exp`,
`Continuous.add`, `Continuous.comp`, …) and the rules compose along the structure of `f`
(Mathlib `fun_prop`). That a denominator has no zeros is established by its positivity. It fails on
a map that is not built so, a discontinuous one in particular. -/
meta def continuousEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "C(ℝ)" <| CasCatalogue.Evidence.closeByFirst
    m!"the map is not established to be continuous"
    [do evalTactic (← `(tactic| fun_prop (disch := (intros; positivity))))]

/-- `f ↦ ∫_a^b f(t) dt`, `C(ℝ) → ℝ`, at the bounds `a b ∈ ℝ`: the binder `∫_{a}^{b} e dt`
(`lean-cas-dsl/specs/binders.md`), its arguments the two bounds. It is Mathlib's interval integral
`∫ t in a..b, f t` (`intervalIntegral`, the oriented Lebesgue integral over `Ι a b`, so that
`∫_b^a f = -∫_a^b f`), which on a continuous map is the Riemann integral: a continuous map is
integrable on every compact interval (`Continuous.intervalIntegrable`), so the operation is total on
`C(ℝ)` at every pair of bounds, and the fundamental theorem of calculus evaluates it
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`, `integral_pow`, `integral_sin`).

The object of maps is `C(ℝ)` and the bound variable ranges over `ℝ`, independently of the bounds:
one object serves all bounds, and a map is admitted with the continuity evidence
`continuousEvidence` of `C(ℝ)`. An integrand continuous on `[a, b]` but not on `ℝ` (`1/t` on
`[1, 2]`) is not admitted by this row; it belongs to `C([a, b])`, a further row of the same
notation. -/
noncomputable def integral (a b : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) :
    continuousMaps ⟶ reals :=
  TypeCat.ofHom fun f =>
    ∫ t in ConcreteCategory.hom (C := Type) a 0..ConcreteCategory.hom (C := Type) b 0, f t

/-- The bound variable of `∫_{a}^{b}` ranges over `ℝ`. -/
abbrev integrationDomain (_ _ : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals) : SetsCat.{0} :=
  reals

/-- The value of `∫_a^b` at an admitted map is Mathlib's interval integral of the map (the
composite applied map by map, its simp-normal form). -/
@[simp] theorem integral_admit (a b : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals)
    (f : ℝ → ℝ) (h : Continuous f) (p : CasCatalogue.Foundation.Objects.fin 1) :
    ConcreteCategory.hom (C := Type) (integral a b)
        (ConcreteCategory.hom (C := Type) (admitContinuous f h) p) =
      ∫ t in ConcreteCategory.hom (C := Type) a 0..ConcreteCategory.hom (C := Type) b 0, f t :=
  rfl

/-- `C^∞(ℝ)`, the smooth maps `ℝ → ℝ`. -/
abbrev smoothMaps : SetsCat.{0} := {f : ℝ → ℝ // ContDiff ℝ (⊤ : ℕ∞) f}

/-- The smooth map `f`, with the evidence that `f` is smooth. -/
def admitSmooth (f : ℝ → ℝ) (h : ContDiff ℝ (⊤ : ℕ∞) f) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ smoothMaps :=
  TypeCat.ofHom fun _ => ⟨f, h⟩

open Lean Elab Tactic in
/-- The evidence that a closed map `f : ℝ → ℝ` is smooth, `ContDiff ℝ ∞ f`: `f` is built as for
`continuousEvidence`, and each constituent is smooth (`Real.contDiff_sin`, `Real.contDiff_exp`,
`ContDiff.mul`, `ContDiff.comp`, `ContDiff.div` away from zeros, …), composed along the structure
of `f` (Mathlib `fun_prop`). It fails on a map that is not built so (`|x|`, `√x`). -/
meta def smoothEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "C^∞(ℝ)" <| CasCatalogue.Evidence.closeByFirst
    m!"the map is not established to be smooth"
    [do evalTactic (← `(tactic| fun_prop (disch := (intros; positivity))))]

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

/-- `k ↦ k!`, `ℕ → ℝˣ`: the image of `k!` under the initial map `ℕ → ℝ`, a unit of `ℝ` because it
is nonzero (`ℝ` is a field of characteristic `0`). -/
noncomputable def factorialUnit :
    CasCatalogue.Foundation.Objects.naturals ⟶ CasCatalogue.Algebra.Units.units ℝ :=
  TypeCat.ofHom fun k =>
    (Ne.isUnit (Nat.cast_ne_zero.mpr k.factorial_ne_zero : ((k.factorial : ℕ) : ℝ) ≠ 0)).unit

/-- `(f, a) ↦ Σ f⁽ᵏ⁾(a)/k! tᵏ`, the division by `k! ∈ ℝˣ` being division by a unit. -/
noncomputable def taylor :
    (smoothMaps × reals : SetsCat.{0}) ⟶ powerSeries ℝ :=
  TypeCat.ofHom fun p =>
    PowerSeries.mk fun k =>
      ConcreteCategory.hom (C := Type) (CasCatalogue.Algebra.Units.divide ℝ)
        (iteratedDeriv k p.1.1 p.2, ConcreteCategory.hom (C := Type) factorialUnit k)

/-- The `k`-th coefficient of the Taylor expansion of `f` at `a` is Mathlib's Taylor coefficient
`f⁽ᵏ⁾(a)/k!` (`taylorCoeffWithin` on `ℝ`). -/
theorem taylor_coeff (f : smoothMaps) (a : ℝ) (k : ℕ) :
    PowerSeries.coeff k (ConcreteCategory.hom (C := Type) taylor (f, a)) =
      taylorCoeffWithin f.1 k Set.univ a := by
  simp [taylor, factorialUnit, CasCatalogue.Algebra.Units.divide, taylorCoeffWithin,
    iteratedDerivWithin_univ, mul_comm]

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
    admission := some `CasCatalogue.Algebra.Calculus.admitContinuous
    evidence := some `CasCatalogue.Algebra.Calculus.continuousEvidence }

normalized_registry .binder
  { id := ⟨"bind.sets.integral"⟩, category := CategoryId.sets, token := "∫"
    operation := `CasCatalogue.Algebra.Calculus.integral
    domain := `CasCatalogue.Algebra.Calculus.integrationDomain }

normalized_registry .object
  { id := ⟨"obj.sets.smooth_maps"⟩, category := CategoryId.sets, name := "C^∞"
    declaration := `CasCatalogue.Algebra.Calculus.smoothMaps
    admission := some `CasCatalogue.Algebra.Calculus.admitSmooth
    evidence := some `CasCatalogue.Algebra.Calculus.smoothEvidence }

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
