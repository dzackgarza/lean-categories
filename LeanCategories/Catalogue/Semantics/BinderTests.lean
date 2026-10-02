/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
public import LeanCategories.Catalogue.Semantics.Algebra.CommutativeMonoids
public import LeanCategories.Catalogue.Semantics.Algebra.Series
public import LeanCategories.Catalogue.Semantics.Algebra.RealLimits
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public meta import LeanCategories.Catalogue.Semantics.EvidenceTests
public meta import LeanCategories.Catalogue.Semantics.Algebra.Series
public meta import LeanCategories.Catalogue.Semantics.Algebra.RealLimits

@[expose] public section

/-!
# The values of the binding operators at admitted maps

Theorems evaluating the operations of the binders `∫_{a}^{b}`, `lim_{t → a}`, `∑_{n ∈ N}`,
`∑_{t ∈ A}`, `∏_{t ∈ A}` at maps admitted into their objects of maps, the points written as the
registered numerals (`NamedRings.ringNumeral`) and named elements (`Calculus.pi`,
`RealLimits.infinity`), and the bodies through the registered operations (`Calculus.sin`,
`Units.divide`) and the map `ℝ ∖ {0} ↪ ℝˣ` (`RealLimits.puncturedUnits`). They hold for every
proof of the admission's
hypothesis. Their expected values are the classical ones, each from its own source:

* `lim_{t → 0} sin t / t = 1` (the derivative of `sin` at `0`; Mathlib `Real.sinc`);
* `lim_{t → ∞} 1/t = 0` (Mathlib `tendsto_inv_atTop_zero`);
* `∫_0^1 t² dt = 1/3` (Mathlib `integral_pow`), `∫_0^π sin t dt = 2` (Mathlib `integral_sin`);
* `∑_{n ∈ ℕ} n² tⁿ ∈ ℤ[[t]]` is the series with coefficients `n²` (`Series.tsum_C_mul_X_pow`);
* `∑_{t ∈ {1, 2, 3}} t² = 14`, `∏_{t ∈ {1, 2, 3}} t = 6` in `ℤ`.

The registered evidence of each object of maps is run, as a consumer runs it, on the hypotheses of
these and further closed maps, and refuses maps outside the object.
-/

open CategoryTheory Filter Topology

namespace CasCatalogue.BinderTests

open CasCatalogue.Foundation.Objects CasCatalogue.Algebra
open CasCatalogue.Algebra.NumberSystems

/-- The registered numeral `k ∈ ℝ`, the image of `k` under the initial ring map `ℤ → ℝ`. -/
noncomputable abbrev realNumeral (k : ℕ) : fin 1 ⟶ reals :=
  NamedRings.ringNumeral ringReals k

@[simp] theorem realNumeral_value (k : ℕ) (p : fin 1) :
    ConcreteCategory.hom (C := Type) (realNumeral k) p = k := by
  simp [realNumeral, NamedRings.ringNumeral]

/-! ## `lim_{t → a}` -/

section Limits

open CasCatalogue.Algebra.RealLimits

/-- The numeral `0 ∈ ℝ` is `0`, so `ℝ ∖ {0} ↪ ℝˣ`. -/
theorem realNumeral_zero : ConcreteCategory.hom (C := Type) (realNumeral 0) 0 = 0 := by simp

/-- `t ↦ sin t / t` on `ℝ ∖ {0}`: `sin` of the inclusion `ℝ ∖ {0} ↪ ℝ`, divided by the unit `t`
(`ℝ ∖ {0} ↪ ℝˣ`). -/
noncomputable def sinOverT : puncturedLine (realNumeral 0) → ℝ := fun t =>
  ConcreteCategory.hom (C := Type) (Units.divide ℝ)
    (ConcreteCategory.hom (C := Type) Calculus.sin
      (ConcreteCategory.hom (C := Type) (puncturedInclusion (realNumeral 0)) t),
     ConcreteCategory.hom (C := Type) (puncturedUnits (realNumeral 0) rfl) t)

/-- **`lim_{t → 0} sin t / t = 1`.** -/
theorem limit_sin_div_self (h : ∃ L, Tendsto sinOverT (approach (realNumeral 0)) (𝓝 L))
    (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (admitConvergent (realNumeral 0) sinOverT h ≫ limit (realNumeral 0)) p = 1 := by
  change ConcreteCategory.hom (C := Type) (limit (realNumeral 0)) ⟨sinOverT, h⟩ = 1
  refine limit_eq _ _ 1 ?_
  change Tendsto sinOverT _ _
  have key := tendsto_approach_of (a := realNumeral 0) (fun t => Real.sin t / t)
    (by rw [realNumeral_zero]; exact tendsto_sin_div_self)
  refine key.congr fun t => ?_
  simp [sinOverT, Units.divide, Calculus.sin, puncturedInclusion, puncturedUnits, div_eq_mul_inv]

/-- `u ↦ 1/u` on `ℝˣ`: the division of `1` by the unit `u`. -/
noncomputable def reciprocal : Units.units ℝ → ℝ := fun u =>
  ConcreteCategory.hom (C := Type) (Units.divide ℝ)
    (ConcreteCategory.hom (C := Type) (realNumeral 1) 0, u)

/-- **`lim_{t → ∞} 1/t = 0`.** -/
theorem limitAtInfinity_reciprocal
    (h : ∃ L, Tendsto reciprocal (approachInfinity infinity) (𝓝 L)) (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (admitConvergentAtInfinity infinity reciprocal h ≫ limitAtInfinity infinity) p = 0 := by
  change ConcreteCategory.hom (C := Type) (limitAtInfinity infinity) ⟨reciprocal, h⟩ = 0
  refine limitAtInfinity_eq _ _ 0 ?_
  change Tendsto reciprocal _ _
  rw [approachInfinity_infinity]
  refine (tendsto_comap_units_of (fun s => s⁻¹) (tendsto_inv_atTop_zero (𝕜 := ℝ))).congr
    fun u => ?_
  simp [reciprocal, Units.divide]

/-- The limit at `−∞` of `1/t` is also `0`. -/
theorem limitAtInfinity_reciprocal_neg
    (h : ∃ L, Tendsto reciprocal (approachInfinity negInfinity) (𝓝 L)) (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (admitConvergentAtInfinity negInfinity reciprocal h ≫ limitAtInfinity negInfinity) p =
        0 := by
  change ConcreteCategory.hom (C := Type) (limitAtInfinity negInfinity) ⟨reciprocal, h⟩ = 0
  refine limitAtInfinity_eq _ _ 0 ?_
  change Tendsto reciprocal _ _
  rw [approachInfinity_negInfinity]
  refine (tendsto_comap_units_of (fun s => s⁻¹) (tendsto_inv_atBot_zero (𝕜 := ℝ))).congr
    fun u => ?_
  simp [reciprocal, Units.divide]

/-- `ℝ ∖ {0} ↪ ℝˣ` exists over `a = 0` only: at `a = 1`, `0 ∈ ℝ ∖ {1}` is not a unit. -/
theorem zero_mem_punctured_one : ∃ t : puncturedLine (realNumeral 1), t.1 = 0 :=
  ⟨⟨0, by simp⟩, rfl⟩

/-- The obligation `a = 0` of `ℝ ∖ {a} ↪ ℝˣ` (`puncturedUnits`) at the point as a consumer forms
it for `lim_{t → 0}`, `id (ringNumeral ringReals 0)`, holds by `rfl`: the evidence tests below
build their maps with `puncturedUnits _ rfl` there. -/
example : id (NamedRings.ringNumeral NumberSystems.ringReals 0) = zeroPoint := rfl

end Limits

/-! ## `∫_{a}^{b}` -/

section Integrals

open CasCatalogue.Algebra.Calculus

/-- **`∫_0^1 t² dt = 1/3`.** -/
theorem integral_sq (h : Continuous fun t : ℝ => t ^ 2) (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (admitContinuous (fun t => t ^ 2) h ≫ integral (realNumeral 0) (realNumeral 1)) p =
      1 / 3 := by
  rw [ConcreteCategory.comp_apply, integral_admit]
  simp [integral_pow]
  norm_num

/-- **`∫_0^π sin t dt = 2`.** -/
theorem integral_sin_zero_pi (h : Continuous fun t : ℝ =>
      ConcreteCategory.hom (C := Type) Calculus.sin t) (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (admitContinuous (fun t => ConcreteCategory.hom (C := Type) Calculus.sin t) h ≫
        integral (realNumeral 0) Calculus.pi) p = 2 := by
  rw [ConcreteCategory.comp_apply, integral_admit]
  simp [Calculus.sin, Calculus.pi, integral_sin]
  norm_num

end Integrals

/-! ## `∑_{n ∈ N}` in `ℤ[[t]]` -/

section Series

open CasCatalogue.Algebra.Series

attribute [local instance] tAdic

/-- `n ↦ n² tⁿ`, `ℕ → ℤ[[t]]`. -/
noncomputable def squaresTimesPowers : ℕ → PowerSeries ℤ :=
  fun n => PowerSeries.C ((n : ℤ) ^ 2) * PowerSeries.X ^ n

/-- **`∑_{n ∈ ℕ} n² tⁿ` is the series with coefficients `n²`**, so its coefficient of `tᵏ` is
`k²`. -/
theorem powerSeriesSum_squares (h : Summable squaresTimesPowers) (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (Series.admit (powerSeriesTAdic (CommRingCat.of ℤ)) naturals squaresTimesPowers h ≫
        powerSeriesSum (CommRingCat.of ℤ) naturals) p =
      PowerSeries.mk fun n => (n : ℤ) ^ 2 :=
  tsum_C_mul_X_pow fun n => (n : ℤ) ^ 2

theorem powerSeriesSum_squares_coeff (h : Summable squaresTimesPowers) (p : fin 1) (k : ℕ) :
    PowerSeries.coeff k (ConcreteCategory.hom (C := Type)
      (Series.admit (powerSeriesTAdic (CommRingCat.of ℤ)) naturals squaresTimesPowers h ≫
        powerSeriesSum (CommRingCat.of ℤ) naturals) p) =
      (k : ℤ) ^ 2 := by
  rw [powerSeriesSum_squares h p, PowerSeries.coeff_mk]

/-- **`∑_{n ∈ ℕ} (1/2)ⁿ = 2`** in `ℝ` (Mathlib `tsum_geometric_two`). -/
theorem realSeriesSum_geometric (h : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n) (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (Series.admit realsTop naturals (fun n => ((1 : ℝ) / 2) ^ n) h ≫ realSeriesSum naturals) p = 2 :=
  tsum_geometric_two

/-- `∑_{n ∈ ℕ} (1/2)ⁿ = 2` in `ℂ`: the sum of the complex series is that of the real one, along
`ℝ ↪ ℂ` (Mathlib `Complex.ofReal_tsum`). -/
theorem complexSeriesSum_geometric (h : Summable fun n : ℕ => ((1 : ℂ) / 2) ^ n) (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (Series.admit complexesTop naturals (fun n => ((1 : ℂ) / 2) ^ n) h ≫ complexSeriesSum naturals) p =
      2 := by
  change ∑' n : ℕ, ((1 : ℂ) / 2) ^ n = 2
  have : (fun n : ℕ => ((1 : ℂ) / 2) ^ n) = fun n => ((((1 : ℝ) / 2) ^ n : ℝ) : ℂ) := by
    funext n; push_cast; ring
  rw [this, ← Complex.ofReal_tsum, tsum_geometric_two]
  norm_num

end Series

/-! ## `∑_{t ∈ A}` and `∏_{t ∈ A}` -/

section FiniteSums

open CasCatalogue.Algebra.FiniteSums CasCatalogue.Algebra.CommMonoids

/-- The finite subset `{1, 2, 3} ⊆ ℤ`. -/
def oneTwoThree : fin 1 ⟶ CasCatalogue.Foundation.FiniteSubsets.finiteSubsets ℤ :=
  TypeCat.ofHom fun _ => {1, 2, 3}

/-- The additive commutative monoid of the ring `ℤ`, along `Ring → AddCommMon`. -/
abbrev integersAdditive : AdditiveCommutativeMonoids.{0} :=
  ringsAdditiveCommutative.toFunctor.obj NamedRings.ringIntegers

/-- The multiplicative commutative monoid of the commutative ring `ℤ`, along `CommRing → CommMon`. -/
abbrev integersMultiplicative : CommutativeMonoids.{0} :=
  commutativeRingsMultiplicative.toFunctor.obj (CommRingCat.of ℤ)

/-- **`∑_{t ∈ {1, 2, 3}} t² = 14`.** -/
theorem sumOver_squares (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (Foundation.Maps.admit ℤ (addCommMonoidCarrier integersAdditive) (fun t => t ^ 2) ≫
        sumOver ℤ integersAdditive oneTwoThree) p = (14 : ℤ) := by
  change ∑ t ∈ ({1, 2, 3} : Finset ℤ), t ^ 2 = 14
  decide

/-- **`∏_{t ∈ {1, 2, 3}} t = 6`.** -/
theorem prodOver_id (p : fin 1) :
    ConcreteCategory.hom (C := Type)
      (Foundation.Maps.admit ℤ (commMonoidCarrier integersMultiplicative) (fun t => t) ≫
        prodOver ℤ integersMultiplicative oneTwoThree) p = (6 : ℤ) := by
  change ∏ t ∈ ({1, 2, 3} : Finset ℤ), t = 6
  decide

end FiniteSums

/-! ## The registered evidence, run on closed maps -/

section Evidence

open CasCatalogue.EvidenceTests

#guard_msgs in
run_meta expectRegistered "obj.sets.convergent_maps" ``RealLimits.convergenceEvidence

#guard_msgs in
run_meta expectRegistered "obj.sets.convergent_maps_at_infinity" ``RealLimits.convergenceEvidence

#guard_msgs in
run_meta expectRegistered "obj.sets.summable_families" ``Series.summableEvidence

-- The maps convergent at their points: `sin t / t` at `0`, `1/t` at `±∞`, `1/t + 3` at `−∞`,
-- `t² + 1` at `2`, `exp t` at `1`.
#guard_msgs in
run_elab do
  expectEstablished RealLimits.convergenceEvidence
    [← `(∃ L, Tendsto CasCatalogue.BinderTests.sinOverT
          (RealLimits.approach (CasCatalogue.BinderTests.realNumeral 0)) (𝓝 L)),
     ← `(∃ L, Tendsto CasCatalogue.BinderTests.reciprocal
          (RealLimits.approachInfinity RealLimits.infinity) (𝓝 L)),
     ← `(∃ L, Tendsto CasCatalogue.BinderTests.reciprocal
          (RealLimits.approachInfinity RealLimits.negInfinity) (𝓝 L)),
     ← `(∃ L, Tendsto (fun u : Units.units ℝ => CasCatalogue.BinderTests.reciprocal u + 3)
          (RealLimits.approachInfinity RealLimits.negInfinity) (𝓝 L)),
     ← `(∃ L, Tendsto (fun t : RealLimits.puncturedLine (CasCatalogue.BinderTests.realNumeral 2) =>
            (ConcreteCategory.hom (C := Type)
              (RealLimits.puncturedInclusion (CasCatalogue.BinderTests.realNumeral 2)) t) ^ 2 + 1)
          (RealLimits.approach (CasCatalogue.BinderTests.realNumeral 2)) (𝓝 L)),
     ← `(∃ L, Tendsto (fun t : RealLimits.puncturedLine (CasCatalogue.BinderTests.realNumeral 1) =>
            ConcreteCategory.hom (C := Type) Calculus.exp
              (ConcreteCategory.hom (C := Type)
                (RealLimits.puncturedInclusion (CasCatalogue.BinderTests.realNumeral 1)) t))
          (RealLimits.approach (CasCatalogue.BinderTests.realNumeral 1)) (𝓝 L))]

-- The statements as a consumer forms them: the numeral `1 ∈ ℝ` as the image of `1` under the
-- initial ring map `ℤ → ℝ` presented through its monoid homomorphism, the unit coerced, the point
-- wrapped in `id`: `lim_{t → ∞} 1/t`, and `lim_{t → 0} sin t / t` with `t ∈ ℝ ∖ {0}`, its
-- quotient written in `ℝ` and as the division by the unit `t ∈ ℝˣ`.
#guard_msgs in
run_elab do
  expectEstablished RealLimits.convergenceEvidence
    [← `(∃ L, Tendsto (fun x : Units.units ℝ =>
            (Int.castRingHom (NamedRings.asRing NumberSystems.ringReals)).toMonoidHom.toOneHom.toFun
              ((1 : ℕ) : ℤ) * ((x⁻¹ : ℝˣ) : ℝ))
          (RealLimits.approachInfinity (id RealLimits.infinity)) (𝓝 L)),
     ← `(∃ L, Tendsto (fun x : RealLimits.puncturedLine
              (id (NamedRings.ringNumeral NumberSystems.ringReals 0)) =>
            Real.sin (x : ℝ) / (x : ℝ))
          (RealLimits.approach (id (NamedRings.ringNumeral NumberSystems.ringReals 0))) (𝓝 L)),
     ← `(∃ L, Tendsto (fun x : RealLimits.puncturedLine
              (id (NamedRings.ringNumeral NumberSystems.ringReals 0)) =>
            Real.sin (x : ℝ) * ((ConcreteCategory.hom (C := Type) (RealLimits.puncturedUnits
              (id (NamedRings.ringNumeral NumberSystems.ringReals 0))
              rfl) x)⁻¹ : ℝˣ))
          (RealLimits.approach (id (NamedRings.ringNumeral NumberSystems.ringReals 0))) (𝓝 L))]

-- `lim_{t → 0} sin t / t` with `t` carried into `ℝˣ` by `ℝ ∖ {0} ↪ ℝˣ` (`puncturedUnits _ rfl`)
-- and back to `ℝ` by the units' inclusion, the quotient the division by the unit `t`; once as
-- that composite of maps, once reduced to `sin ↑(Units.mk0 ↑t _) * ↑(Units.mk0 ↑t _)⁻¹`.
#guard_msgs in
run_elab do
  expectEstablished RealLimits.convergenceEvidence
    [← `(∃ L, Tendsto (fun x : RealLimits.puncturedLine
              (id (NamedRings.ringNumeral NumberSystems.ringReals 0)) =>
            ConcreteCategory.hom (C := Type) (Units.divide ℝ)
              (Real.sin (ConcreteCategory.hom (C := Type)
                  (RealLimits.puncturedUnits _ rfl ≫ Units.inclusion ℝ) x),
               ConcreteCategory.hom (C := Type) (RealLimits.puncturedUnits _ rfl) x))
          (RealLimits.approach (id (NamedRings.ringNumeral NumberSystems.ringReals 0))) (𝓝 L)),
     ← `(∃ L, Tendsto (fun x : RealLimits.puncturedLine
              (id (NamedRings.ringNumeral NumberSystems.ringReals 0)) =>
            Real.sin ((Units.mk0 (x : ℝ) fun h0 =>
                x.2 (h0.trans (RealLimits.value_eq_zero_of_eq rfl).symm) : ℝˣ) : ℝ) *
              (((Units.mk0 (x : ℝ) fun h0 =>
                x.2 (h0.trans (RealLimits.value_eq_zero_of_eq rfl).symm) : ℝˣ)⁻¹ : ℝˣ) : ℝ))
          (RealLimits.approach (id (NamedRings.ringNumeral NumberSystems.ringReals 0))) (𝓝 L))]

-- The same statement in the exact form the consumer's kernel produces: the variable passed
-- through the identity morphism of `ℝ ∖ {0}` wrapped in `id` (`.hom'.toFun`), `puncturedUnits`
-- unfolded to `Units.mk0 x.val h` with `h` its own proof of `t ≠ 0` applied to that image of `x`.
-- The proof is read off the definition of `puncturedUnits`, not named. Its type is `x.val ≠ 0`
-- only up to unfolding, so `Units.val_mk0` does not rewrite it; the evidence reads
-- `↑(Units.mk0 a _)` as `a` by definition (`RealLimits.collapseUnits`).
open Lean Meta Elab Term in
/-- `∃ L, Tendsto (fun x => sin ↑(Units.mk0 ↑x h) * ↑(Units.mk0 ↑x h)⁻¹) (t → 0) (𝓝 L)`, with `h`
the proof inside `puncturedUnits` at `t = (id (𝟙 (ℝ ∖ {0}))).hom'.toFun x`. -/
meta def kernelSincStatement : TermElabM Term := do
  let some value := (← getConstInfo ``RealLimits.puncturedUnits).value?
    | throwError "puncturedUnits has no definition"
  let some mk0 := value.find? (·.isAppOfArity ``Units.mk0 4)
    | throwError "puncturedUnits is not built from Units.mk0"
  let proof := mk0.appArg!.getAppFn
  unless proof.isConst do throwError "the proof inside puncturedUnits is not a constant"
  let point ← elabTerm (← `(id (NamedRings.ringNumeral NumberSystems.ringReals 0))) none
  let domain ← elabTerm (← `(RealLimits.puncturedLine
    (id (NamedRings.ringNumeral NumberSystems.ringReals 0)))) none
  synthesizeSyntheticMVarsNoPostponing
  let map ← withLocalDeclD `x domain fun x => do
    let image ← elabTerm (← `((id (CategoryStruct.id (RealLimits.puncturedLine
      (id (NamedRings.ringNumeral NumberSystems.ringReals 0))))).hom'.toFun $(← exprToSyntax x)))
      none
    synthesizeSyntheticMVarsNoPostponing
    let h := mkApp3 proof point (← mkEqRefl point) image
    let unit ← mkAppM ``Units.mk0 #[← mkAppM ``Subtype.val #[x], h]
    let body ← mkAppM ``HMul.hMul #[← mkAppM ``Real.sin #[← mkAppM ``Units.val #[unit]],
      ← mkAppM ``Units.val #[← mkAppM ``Inv.inv #[unit]]]
    mkLambdaFVars #[x] (← instantiateMVars body)
  `(∃ L : ℝ, Tendsto $(← exprToSyntax map)
      (RealLimits.approach (id (NamedRings.ringNumeral NumberSystems.ringReals 0))) (𝓝 L))

#guard_msgs in
run_elab do
  expectEstablished RealLimits.convergenceEvidence [← kernelSincStatement]

-- Maps that do not converge: `sin(1/t)` at `0`, `t` and `sin t` at `∞`.
#guard_msgs in
run_elab do
  expectRefused RealLimits.convergenceEvidence
    [← `(∃ L, Tendsto (fun t : RealLimits.puncturedLine (CasCatalogue.BinderTests.realNumeral 0) =>
            Real.sin (ConcreteCategory.hom (C := Type) (RealLimits.puncturedUnits
              (CasCatalogue.BinderTests.realNumeral 0) rfl) t)⁻¹.1)
          (RealLimits.approach (CasCatalogue.BinderTests.realNumeral 0)) (𝓝 L)),
     ← `(∃ L, Tendsto (fun u : Units.units ℝ => (u : ℝ))
          (RealLimits.approachInfinity RealLimits.infinity) (𝓝 L)),
     ← `(∃ L, Tendsto (fun u : Units.units ℝ => Real.sin (u : ℝ))
          (RealLimits.approachInfinity RealLimits.infinity) (𝓝 L))]

attribute [local instance] Series.tAdic

-- Summable families: `n² tⁿ`, `n tⁿ + tⁿ⁺¹` in `ℤ[[t]]`, `(1/2)ⁿ`, `1/n²` in `ℝ`.
#guard_msgs in
run_elab do
  expectEstablished Series.summableEvidence
    [← `(Summable CasCatalogue.BinderTests.squaresTimesPowers),
     ← `(Summable fun n : ℕ => (n : ℤ) • (PowerSeries.X : PowerSeries ℤ) ^ n +
            (PowerSeries.X : PowerSeries ℤ) ^ (n + 1)),
     ← `(Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n),
     ← `(Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)]

-- The admission's hypothesis is stated at the object `Y` of Hausdorff commutative topological
-- monoids, with `Y`'s addition and topology: `(1/2)ⁿ` at `ℝ`, `n² tⁿ` at `ℤ[[t]]` `(t)`-adically.
#guard_msgs in
run_elab do
  expectEstablished Series.summableEvidence
    [← `(Summable (fun n : ℕ =>
            (((1 : ℝ) / 2) ^ n : Series.asTopMonoid Series.realsTop))),
     ← `(Summable (CasCatalogue.BinderTests.squaresTimesPowers :
            ℕ → Series.asTopMonoid (Series.powerSeriesTAdic (CommRingCat.of ℤ))))]

#guard_msgs in
run_elab do
  expectRefused Series.summableEvidence
    [← `(Summable (fun _ : ℕ => ((1 : ℝ) : Series.asTopMonoid Series.realsTop)))]

-- Families that are not summable: `t⁰` repeated in `ℤ[[t]]`, `1` and `1/n` in `ℝ`.
#guard_msgs in
run_elab do
  expectRefused Series.summableEvidence
    [← `(Summable fun _ : ℕ => (PowerSeries.X : PowerSeries ℤ) ^ 0),
     ← `(Summable fun _ : ℕ => (1 : ℝ)),
     ← `(Summable fun n : ℕ => (1 : ℝ) / (n : ℝ))]

end Evidence

end CasCatalogue.BinderTests
