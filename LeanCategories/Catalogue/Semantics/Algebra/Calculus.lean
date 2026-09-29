/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public import LeanCategories.Catalogue.Semantics.Foundation.PartialMaps
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Elementary calculus (SPEC.md, "Elementary calculus")

Real functions and the partial operations of calculus, each defined exactly where its
mathematics is (maps into `ℝ⊥`, the partial map classifier):
* `sin`, `cos`, `exp : ℝ → ℝ` and `π : 1 → ℝ` (Mathlib `Real.sin`, `Real.cos`, `Real.exp`,
  `Real.pi`);
* division `ℝ × ℝ → ℝ⊥`, undefined at a zero divisor;
* for `f : ℝ → ℝ⊥` with domain `D = {t | f t defined}`, `lim_{t → a} f(t)`, defined when `a` is an
  accumulation point of `D` and `f|_D` tends to a limit on `D ∖ {a}` (Mathlib `Filter.Tendsto`,
  `nhdsWithin`), and `lim_{t → ∞} f(t)` along `atTop`, defined when `D` is unbounded above;
* `∫_a^b f`, defined when `f` is interval integrable on `[a, b]` (Mathlib `intervalIntegral`);
* `ℝ[[t]]` (Mathlib `PowerSeries`) and the Taylor expansion `a ↦ Σ f⁽ᵏ⁾(a)/k! tᵏ` of `f : ℝ → ℝ`,
  defined where `f` is smooth (Mathlib `ContDiffAt`, `iteratedDeriv`).
-/

open CategoryTheory Filter Topology

namespace CasCatalogue.Algebra.Calculus

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.PartialMaps
  CasCatalogue.Algebra.NumberSystems

/-- `sin : ℝ → ℝ`. -/
noncomputable def sin : reals ⟶ reals := TypeCat.ofHom Real.sin

/-- `cos : ℝ → ℝ`. -/
noncomputable def cos : reals ⟶ reals := TypeCat.ofHom Real.cos

/-- `exp : ℝ → ℝ`. -/
noncomputable def exp : reals ⟶ reals := TypeCat.ofHom Real.exp

/-- `π ∈ ℝ`. -/
noncomputable def pi : CasCatalogue.Foundation.Objects.fin 1 ⟶ reals :=
  TypeCat.ofHom fun _ => Real.pi

open Classical in
/-- `a / b`, undefined at `b = 0`. -/
noncomputable def divide : (reals × reals : SetsCat.{0}) ⟶ partialValues ℝ :=
  TypeCat.ofHom fun p => if p.2 = 0 then none else some (p.1 / p.2)

/-- The domain `{t | f t defined}` of a partial map. -/
def domain (f : reals ⟶ partialValues ℝ) : Set ℝ :=
  {t | (ConcreteCategory.hom (C := Type) f t).isSome}

/-- `f` on its domain. -/
def onDomain (f : reals ⟶ partialValues ℝ) (t : domain f) : ℝ :=
  (ConcreteCategory.hom (C := Type) f t.1).get t.2

open Classical in
/-- The limit of `f|_D` along the filter `F` on `D`, where `F` is proper. -/
noncomputable def limitAlong (f : reals ⟶ partialValues ℝ) (F : Filter (domain f)) : Option ℝ :=
  if h : F.NeBot ∧ ∃ L, Tendsto (onDomain f) F (𝓝 L) then some (Classical.choose h.2) else none

/-- `a ↦ lim_{t → a} f(t)`, on the punctured neighbourhoods of `a` in the domain of `f`. -/
noncomputable def limitAt (f : reals ⟶ partialValues ℝ) : reals ⟶ partialValues ℝ :=
  TypeCat.ofHom fun a => limitAlong f (comap Subtype.val (𝓝[≠] a))

/-- `lim_{t → ∞} f(t)`. -/
noncomputable def limitAtTop (f : reals ⟶ partialValues ℝ) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ partialValues ℝ :=
  TypeCat.ofHom fun _ => limitAlong f (comap Subtype.val atTop)

open Classical in
/-- `(a, b) ↦ ∫_a^b f`, defined when `f` is interval integrable on `[a, b]`. -/
noncomputable def integral (f : reals ⟶ reals) : (reals × reals : SetsCat.{0}) ⟶ partialValues ℝ :=
  TypeCat.ofHom fun p =>
    if IntervalIntegrable (ConcreteCategory.hom (C := Type) f) MeasureTheory.volume p.1 p.2 then
      some (∫ t in p.1..p.2, ConcreteCategory.hom (C := Type) f t)
    else none

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

open Classical in
/-- `a ↦ Σ f⁽ᵏ⁾(a)/k! tᵏ`, defined where `f` is smooth. -/
noncomputable def taylor (f : reals ⟶ reals) : reals ⟶ partialValues (PowerSeries ℝ) :=
  TypeCat.ofHom fun a =>
    if ContDiffAt ℝ (⊤ : ℕ∞) (ConcreteCategory.hom (C := Type) f) a then
      some (PowerSeries.mk fun k =>
        iteratedDeriv k (ConcreteCategory.hom (C := Type) f) a / k.factorial)
    else none

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

normalized_registry .morphism
  { id := ⟨"mor.sets.real_partial_divide"⟩, category := CategoryId.sets, name := "partial /"
    declaration := `CasCatalogue.Algebra.Calculus.divide }

normalized_registry .morphism
  { id := ⟨"mor.sets.real_limit_at"⟩, category := CategoryId.sets, name := "lim"
    declaration := `CasCatalogue.Algebra.Calculus.limitAt }

normalized_registry .morphism
  { id := ⟨"mor.sets.real_limit_at_top"⟩, category := CategoryId.sets, name := "lim ∞"
    declaration := `CasCatalogue.Algebra.Calculus.limitAtTop }

normalized_registry .morphism
  { id := ⟨"mor.sets.real_integral"⟩, category := CategoryId.sets, name := "∫ₐᵇ"
    declaration := `CasCatalogue.Algebra.Calculus.integral }

normalized_registry .object
  { id := ⟨"obj.sets.power_series"⟩, category := CategoryId.sets, name := "PowerSeries"
    declaration := `CasCatalogue.Algebra.Calculus.powerSeries
    generator := some `CasCatalogue.Algebra.Calculus.powerSeriesGenerator
    constants := some `CasCatalogue.Algebra.Calculus.powerSeriesConstants }

normalized_registry .morphism
  { id := ⟨"mor.sets.taylor_expansion"⟩, category := CategoryId.sets, name := "taylor_expansion"
    declaration := `CasCatalogue.Algebra.Calculus.taylor }

end CasCatalogue
