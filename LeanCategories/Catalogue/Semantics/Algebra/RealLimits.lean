/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence

@[expose] public section

/-!
# Limits of real functions (`lim_{t → a} e`)

The limit of `f` at a point `a` of the extended real line `ℝ̄ = [−∞, +∞]` (Mathlib `EReal`) is the
value `L` such that `f(t) → L` as `t` tends to `a` through the points of `f`'s domain other than
`a`: `f` tends to `L` along the punctured neighbourhoods of `a` (Mathlib `Filter.Tendsto f (𝓝[≠] a)
(𝓝 L)`; Bourbaki, *General Topology*, I.7.3). The limit is defined on the maps that converge at
`a`, and there it is unique, because `ℝ` is Hausdorff and every punctured neighbourhood of `a`
meets the domain (`tendsto_nhds_unique`). So `lim_{t → a}` is a total map out of the object of maps
convergent at `a` (LC-14): the binder `lim_{t → a} e` (`lean-cas-dsl/specs/binders.md`), whose
argument is the point `a`. A map is admitted there only with the evidence that it converges.

`ℝ̄` is `ℝ` with the two points `±∞` (`ℝ ⊆ ℝ̄`, `realsExtendedReals`); its points at infinity form
`ℝ̄ ∖ ℝ = {−∞, +∞}` (`infinities`), with `∞ = +∞` and `-∞` named. The limit has two rows, by
where `a` lies in `ℝ̄ = ℝ ⊔ {±∞}`:

* `a ∈ ℝ`. The bound variable ranges over `ℝ ∖ {a}` (`puncturedLine a`), the largest set of reals
  on which a map can have a limit at `a` without being evaluated at `a`; it tends to `a` along
  `𝓝[≠] a`, traced on `ℝ ∖ {a}` (`approach a`).
* `a = ±∞`. The punctured neighbourhoods of `±∞` in `ℝ̄` traced on `ℝ` are the half-lines
  `(M, ∞)`, `(−∞, M)` (Mathlib `EReal.nhdsWithin_top`, `EReal.nhdsWithin_bot`: the filters
  `atTop`, `atBot`), so the limit depends only on the map on a half-line, and any domain
  containing one serves. The bound variable ranges over `ℝ ∖ {0} = ℝˣ` (`Algebra.Units`): it
  contains a half-line at each of `±∞`, so one domain serves both, and it is where `t ↦ 1/t` is a
  map (`1/t` is the division by the unit `t`, LC-16), the standard domain of `lim_{t → ∞} 1/t`.

Division by the bound variable of the first row needs `t ∈ ℝˣ`. The inclusion
`ℝ ∖ {a} ↪ ℝˣ` exists exactly when `a = 0` (`puncturedUnits`, a monomorphism over the
obligation `a = 0`; not a registered inclusion, since an inclusion row relates its objects at the
declaration's own parameters): for `a ≠ 0`, `0 ∈ ℝ ∖ {a}` is not a unit, and a body
dividing by `t` is not a map on `ℝ ∖ {a}`; a body dividing by `t - a` divides by a unit only once
`t - a` is (the map `ℝ ∖ {a} → ℝˣ`, `t ↦ t - a`, which is again an inclusion over the fibre `a`).
-/

open CategoryTheory Filter Topology

/-!
The intrinsic comparison with the generic filter limit is `limit_eq_limUnder` and
`limitAtInfinity_eq_limUnder`. These use Mathlib's `tendsto_nhds_limUnder` on the
admitted convergence proof; the converse characterizations use uniqueness on the
nonbottom approach filters. Thus no value of Mathlib's totalized `limUnder` off
its convergence domain is exposed by either binder.

Reuse search (2026-10-02, LC-09): the live formalization corpus was searched for
`limUnder_eq`, `tendsto_nhds_limUnder`, `"limit" "Hausdorff"`, and
`"convergent" "limUnder"`. The generic owners are Mathlib
`Topology/Basic.lean::tendsto_nhds_limUnder` and
`Topology/Separation/Hausdorff.lean::Filter.Tendsto.limUnder_eq`, inspected at the
project's pin `db584cd6d46c92f209a44c0f1c829460d327499d`. Their hypotheses are
exactly convergence and, for uniqueness, a Hausdorff codomain and a nonbottom
source filter; `approach_neBot` and `approachInfinity_neBot` supply the latter.
-/

namespace CasCatalogue.Algebra.RealLimits

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects
open CasCatalogue.Algebra.NumberSystems

/-! ### The extended real line -/

/-- `ℝ̄ = [−∞, +∞]` (Mathlib `EReal`). -/
abbrev extendedReals : SetsCat.{0} := EReal

/-- `ℝ ⊆ ℝ̄` (Mathlib `Real.toEReal`). -/
def realsExtendedReals : reals ⟶ extendedReals := TypeCat.ofHom Real.toEReal

/-- `ℝ ↪ ℝ̄` is a monomorphism (Mathlib `EReal.coe_injective`). -/
theorem realsExtendedReals_mono : Mono realsExtendedReals :=
  mono_of_injective _ EReal.coe_injective

/-- `ℝ̄ ∖ ℝ = {−∞, +∞}`, the points at infinity. -/
abbrev infinities : SetsCat.{0} := {a : EReal // a = ⊥ ∨ a = ⊤}

/-- `{−∞, +∞} ↪ ℝ̄`. -/
def infinitiesInclusion : infinities ⟶ extendedReals := TypeCat.ofHom Subtype.val

/-- `∞ = +∞ ∈ ℝ̄ ∖ ℝ`. -/
noncomputable def infinity : fin 1 ⟶ infinities := TypeCat.ofHom fun _ => ⟨⊤, Or.inr rfl⟩

/-- `-∞ ∈ ℝ̄ ∖ ℝ`. -/
noncomputable def negInfinity : fin 1 ⟶ infinities := TypeCat.ofHom fun _ => ⟨⊥, Or.inl rfl⟩

/-- The points at infinity are not reals. -/
theorem infinities_not_real (a : infinities) (x : ℝ) : a.1 ≠ (x : EReal) := by
  rcases a.2 with h | h <;> rw [h] <;> simp

/-! ### Limits at a real point -/

/-- `ℝ ∖ {a}`. -/
abbrev puncturedLine (a : fin 1 ⟶ reals) : SetsCat.{0} :=
  {t : ℝ // t ≠ ConcreteCategory.hom (C := Type) a 0}

/-- `ℝ ∖ {a} ↪ ℝ`. -/
def puncturedInclusion (a : fin 1 ⟶ reals) : puncturedLine a ⟶ reals :=
  TypeCat.ofHom Subtype.val

/-- `t → a` in `ℝ ∖ {a}`: the punctured neighbourhoods `𝓝[≠] a` of `a`, traced on `ℝ ∖ {a}`. -/
def approach (a : fin 1 ⟶ reals) : Filter (puncturedLine a) :=
  comap Subtype.val (𝓝[≠] ConcreteCategory.hom (C := Type) a 0)

/-- Every punctured neighbourhood of `a` meets `ℝ ∖ {a}`: `ℝ` has no isolated point
(`NormedField.nhdsNE_neBot`), and `ℝ ∖ {a}` is itself one. -/
instance approach_neBot (a : fin 1 ⟶ reals) : (approach a).NeBot :=
  NeBot.comap_of_range_mem inferInstance
    (by rw [Subtype.range_coe_subtype]; exact self_mem_nhdsWithin)

/-- The maps `ℝ ∖ {a} → ℝ` that converge at `a`. -/
structure ConvergentAt (a : fin 1 ⟶ reals) : Type where
  /-- The map. -/
  toFun : puncturedLine a → ℝ
  /-- It converges at `a`. -/
  converges : ∃ L, Tendsto toFun (approach a) (𝓝 L)

/-- The maps convergent at `a ∈ ℝ`. -/
abbrev convergentMaps (a : fin 1 ⟶ reals) : SetsCat.{0} := ConvergentAt a

/-- The map `f`, with the evidence that it converges at `a`. -/
def admitConvergent (a : fin 1 ⟶ reals) (f : puncturedLine a → ℝ)
    (h : ∃ L, Tendsto f (approach a) (𝓝 L)) : fin 1 ⟶ convergentMaps a :=
  TypeCat.ofHom fun _ => ⟨f, h⟩

/-- `f ↦ lim_{t → a} f(t)`, the limit at `a ∈ ℝ` of a map convergent there: the value its
convergence carries, which is the unique limit (`limit_eq`). The binder `lim_{t → a} e`. -/
noncomputable def limit (a : fin 1 ⟶ reals) : convergentMaps a ⟶ reals :=
  TypeCat.ofHom fun f => Classical.choose f.converges

/-- The bound variable of `lim_{t → a}` ranges over `ℝ ∖ {a}`. -/
abbrev limitDomain (a : fin 1 ⟶ reals) : SetsCat.{0} := puncturedLine a

/-- The map tends to its limit. -/
theorem tendsto_limit (a : fin 1 ⟶ reals) (f : convergentMaps a) :
    Tendsto f.toFun (approach a) (𝓝 (ConcreteCategory.hom (C := Type) (limit a) f)) :=
  Classical.choose_spec f.converges

/-- The limit is unique: a value `L` that the map tends to at `a` is its limit. -/
theorem limit_eq (a : fin 1 ⟶ reals) (f : convergentMaps a) (L : ℝ)
    (h : Tendsto f.toFun (approach a) (𝓝 L)) :
    ConcreteCategory.hom (C := Type) (limit a) f = L :=
  tendsto_nhds_unique (tendsto_limit a f) h

/-- The admitted limit agrees with Mathlib's generic filter limit on its actual domain. -/
theorem limit_eq_limUnder (a : fin 1 ⟶ reals) (f : convergentMaps a) :
    ConcreteCategory.hom (C := Type) (limit a) f = limUnder (approach a) f.toFun :=
  limit_eq a f _ (tendsto_nhds_limUnder f.converges)

/-- A value is the admitted limit exactly when the admitted map tends to it. -/
theorem limit_eq_iff_tendsto (a : fin 1 ⟶ reals) (f : convergentMaps a) (L : ℝ) :
    ConcreteCategory.hom (C := Type) (limit a) f = L ↔
      Tendsto f.toFun (approach a) (𝓝 L) :=
  ⟨fun h => h ▸ tendsto_limit a f, limit_eq a f L⟩

/-- A map `f` on `ℝ ∖ {a}` that is the restriction of a map `g` defined near `a` tends to `L` at
`a` when `g` tends to `L` along `𝓝[≠] a`. -/
theorem tendsto_approach_of {a : fin 1 ⟶ reals} (g : ℝ → ℝ) {L : ℝ}
    (h : Tendsto g (𝓝[≠] ConcreteCategory.hom (C := Type) a 0) (𝓝 L)) :
    Tendsto (fun t : puncturedLine a => g t.1) (approach a) (𝓝 L) :=
  h.comp tendsto_comap

/-- The point `0 ∈ ℝ`: the numeral `0` of the ring `ℝ`, the image of `0` under the initial ring
map `ℤ → ℝ` (`NamedRings.ringNumeral`, LC-15). -/
noncomputable abbrev zeroPoint : fin 1 ⟶ reals :=
  CasCatalogue.Algebra.NamedRings.ringNumeral CasCatalogue.Algebra.NumberSystems.ringReals 0

/-- The value of the point `0 ∈ ℝ` is `0`. -/
theorem zeroPoint_value (p : fin 1) : ConcreteCategory.hom (C := Type) zeroPoint p = 0 := by
  simp [CasCatalogue.Algebra.NamedRings.ringNumeral]

/-- At a point `a = 0`, the value of `a` is `0`. -/
theorem value_eq_zero_of_eq {a : fin 1 ⟶ reals} (h : a = zeroPoint) :
    ConcreteCategory.hom (C := Type) a 0 = 0 := by
  subst h
  exact zeroPoint_value 0

/-- `ℝ ∖ {a} ↪ ℝˣ` over the point `a = 0`: the reals other than `0` are the units of the field `ℝ`
(Mathlib `Units.mk0`). The obligation `h : a = 0` is an equation of points of `ℝ`, `0` the
registered numeral (`zeroPoint`). For `a ≠ 0` there is no such map, since `0 ∈ ℝ ∖ {a}` is not a
unit. -/
noncomputable def puncturedUnits (a : fin 1 ⟶ reals) (h : a = zeroPoint) :
    puncturedLine a ⟶ CasCatalogue.Algebra.Units.units ℝ :=
  TypeCat.ofHom fun t => Units.mk0 t.1 fun h0 => t.2 (h0.trans (value_eq_zero_of_eq h).symm)

/-- `ℝ ∖ {0} ↪ ℝˣ` is a monomorphism, through which `ℝ ∖ {0} ↪ ℝ` factors: a unit is its value. -/
theorem puncturedUnits_mono (a : fin 1 ⟶ reals) (h : a = zeroPoint) :
    Mono (puncturedUnits a h) :=
  mono_of_injective _ fun _ _ hst => Subtype.ext (congrArg Units.val hst :)

/-- `ℝ ∖ {0} → ℝˣ → ℝ` is `ℝ ∖ {0} ↪ ℝ`. -/
theorem puncturedUnits_inclusion (a : fin 1 ⟶ reals) (h : a = zeroPoint) :
    puncturedUnits a h ≫ CasCatalogue.Algebra.Units.inclusion ℝ = puncturedInclusion a :=
  rfl

/-! ### Limits at `±∞` -/

/-- `t → a` for `a = ±∞`: the punctured neighbourhoods of `a` in `ℝ̄`, traced on `ℝˣ ⊆ ℝ ⊆ ℝ̄`. -/
noncomputable def approachInfinity (a : fin 1 ⟶ infinities) :
    Filter (CasCatalogue.Algebra.Units.units ℝ) :=
  comap Units.val (comap Real.toEReal (𝓝[≠] (ConcreteCategory.hom (C := Type) a 0).1))

/-- The punctured neighbourhoods of `+∞` traced on `ℝ` are `atTop` (Mathlib
`EReal.nhdsWithin_top`; `ℝ ↪ ℝ̄` is injective). -/
theorem comap_nhdsNE_top : comap Real.toEReal (𝓝[≠] (⊤ : EReal)) = atTop := by
  rw [EReal.nhdsWithin_top, comap_map EReal.coe_injective]

/-- The punctured neighbourhoods of `−∞` traced on `ℝ` are `atBot`. -/
theorem comap_nhdsNE_bot : comap Real.toEReal (𝓝[≠] (⊥ : EReal)) = atBot := by
  rw [EReal.nhdsWithin_bot, comap_map EReal.coe_injective]

/-- `t → +∞` in `ℝˣ` is `atTop` traced on `ℝˣ`. -/
theorem approachInfinity_infinity :
    approachInfinity infinity = comap Units.val atTop :=
  congrArg (comap Units.val) comap_nhdsNE_top

/-- `t → −∞` in `ℝˣ` is `atBot` traced on `ℝˣ`. -/
theorem approachInfinity_negInfinity :
    approachInfinity negInfinity = comap Units.val atBot :=
  congrArg (comap Units.val) comap_nhdsNE_bot

/-- Every half-line at `±∞` meets `ℝˣ`: it contains a half-line `(1, ∞)` or `(−∞, −1)` of units. -/
instance approachInfinity_neBot (a : fin 1 ⟶ infinities) : (approachInfinity a).NeBot := by
  rcases (ConcreteCategory.hom (C := Type) a 0).2 with h | h
  · rw [approachInfinity, h, comap_nhdsNE_bot]
    refine NeBot.comap_of_range_mem inferInstance (mem_atBot_sets.mpr ⟨-1, fun x hx => ?_⟩)
    exact ⟨Units.mk0 x (by linarith : x ≠ 0), rfl⟩
  · rw [approachInfinity, h, comap_nhdsNE_top]
    refine NeBot.comap_of_range_mem inferInstance (mem_atTop_sets.mpr ⟨1, fun x hx => ?_⟩)
    exact ⟨Units.mk0 x (by linarith : x ≠ 0), rfl⟩

/-- The maps `ℝˣ → ℝ` that converge at `a = ±∞`. -/
structure ConvergentAtInfinity (a : fin 1 ⟶ infinities) : Type where
  /-- The map. -/
  toFun : CasCatalogue.Algebra.Units.units ℝ → ℝ
  /-- It converges at `a`. -/
  converges : ∃ L, Tendsto toFun (approachInfinity a) (𝓝 L)

/-- The maps convergent at `a = ±∞`. -/
abbrev convergentMapsAtInfinity (a : fin 1 ⟶ infinities) : SetsCat.{0} := ConvergentAtInfinity a

/-- The map `f`, with the evidence that it converges at `a = ±∞`. -/
def admitConvergentAtInfinity (a : fin 1 ⟶ infinities)
    (f : CasCatalogue.Algebra.Units.units ℝ → ℝ) (h : ∃ L, Tendsto f (approachInfinity a) (𝓝 L)) :
    fin 1 ⟶ convergentMapsAtInfinity a :=
  TypeCat.ofHom fun _ => ⟨f, h⟩

/-- `f ↦ lim_{t → a} f(t)` at `a = ±∞`, the unique limit (`limitAtInfinity_eq`). The binder
`lim_{t → ∞} e`. -/
noncomputable def limitAtInfinity (a : fin 1 ⟶ infinities) : convergentMapsAtInfinity a ⟶ reals :=
  TypeCat.ofHom fun f => Classical.choose f.converges

/-- The bound variable of `lim_{t → ±∞}` ranges over `ℝ ∖ {0} = ℝˣ`. -/
abbrev limitAtInfinityDomain (_ : fin 1 ⟶ infinities) : SetsCat.{0} :=
  CasCatalogue.Algebra.Units.units ℝ

/-- The map tends to its limit at `±∞`. -/
theorem tendsto_limitAtInfinity (a : fin 1 ⟶ infinities) (f : convergentMapsAtInfinity a) :
    Tendsto f.toFun (approachInfinity a)
      (𝓝 (ConcreteCategory.hom (C := Type) (limitAtInfinity a) f)) :=
  Classical.choose_spec f.converges

/-- The limit at `±∞` is unique. -/
theorem limitAtInfinity_eq (a : fin 1 ⟶ infinities) (f : convergentMapsAtInfinity a) (L : ℝ)
    (h : Tendsto f.toFun (approachInfinity a) (𝓝 L)) :
    ConcreteCategory.hom (C := Type) (limitAtInfinity a) f = L :=
  tendsto_nhds_unique (tendsto_limitAtInfinity a f) h

/-- The admitted limit at infinity agrees with Mathlib's generic filter limit. -/
theorem limitAtInfinity_eq_limUnder (a : fin 1 ⟶ infinities)
    (f : convergentMapsAtInfinity a) :
    ConcreteCategory.hom (C := Type) (limitAtInfinity a) f =
      limUnder (approachInfinity a) f.toFun :=
  limitAtInfinity_eq a f _ (tendsto_nhds_limUnder f.converges)

/-- A value is the admitted limit at infinity exactly when the admitted map tends to it. -/
theorem limitAtInfinity_eq_iff_tendsto (a : fin 1 ⟶ infinities)
    (f : convergentMapsAtInfinity a) (L : ℝ) :
    ConcreteCategory.hom (C := Type) (limitAtInfinity a) f = L ↔
      Tendsto f.toFun (approachInfinity a) (𝓝 L) :=
  ⟨fun h => h ▸ tendsto_limitAtInfinity a f, limitAtInfinity_eq a f L⟩

/-- A map `f` on `ℝˣ` that is the restriction of a map `g` on `ℝ` tends to `L` as `t → G` in `ℝˣ`
when `g` tends to `L` along `G`. -/
theorem tendsto_comap_units_of (g : ℝ → ℝ) {G : Filter ℝ} {L : ℝ} (h : Tendsto g G (𝓝 L)) :
    Tendsto (fun u : CasCatalogue.Algebra.Units.units ℝ => g u.1) (comap Units.val G) (𝓝 L) :=
  h.comp tendsto_comap

/-! ### Standard limits -/

/-- `sin t / t → 1` as `t → 0`, `t ≠ 0`: `sin t / t` is the cardinal sine away from `0`
(Mathlib `Real.sinc_of_ne_zero`), which is continuous with value `1` at `0`
(`Real.continuous_sinc`, `Real.sinc_zero`). -/
theorem tendsto_sin_div_self : Tendsto (fun t : ℝ => Real.sin t / t) (𝓝[≠] 0) (𝓝 1) := by
  have h : Tendsto Real.sinc (𝓝[≠] 0) (𝓝 1) := by
    simpa [Real.sinc_zero] using (Real.continuous_sinc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine h.congr' (eventually_of_mem self_mem_nhdsWithin fun t ht => ?_)
  exact Real.sinc_of_ne_zero ht

/-- `sin t · t⁻¹ → 1` as `t → 0`, `t ≠ 0`. -/
theorem tendsto_sin_mul_inv_self : Tendsto (fun t : ℝ => Real.sin t * t⁻¹) (𝓝[≠] 0) (𝓝 1) := by
  simpa only [div_eq_mul_inv] using tendsto_sin_div_self

/-! ### The evidence of convergence -/

open Lean Meta Elab Tactic

/-- The value of a unit `Units.mk0 a h ∈ ℝˣ` is `a`, by definition (Mathlib `Units.mk0`,
`Units.val_mk0`): replace each `↑(Units.mk0 a h)` in the main goal by `a`, whatever the proof `h`.
`Units.val_mk0` as a rewrite rule does not apply when the type of `h` is `a ≠ 0` only up to
unfolding (`h` about `((id (𝟙 _)).hom'.toFun x).val` for `a = x.val`); the equation holds
definitionally all the same, and the goal is changed along it. -/
meta def collapseUnits : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let collapsed := target.replace fun e =>
    if e.isAppOfArity ``Units.val 3 && e.appArg!.isAppOfArity ``Units.mk0 4 then
      some e.appArg!.appFn!.appArg!
    else none
  unless collapsed == target do
    replaceMainGoal [← goal.change collapsed]

/-- Unfold the catalogue's operations and points in the main goal to the Mathlib terms they are
defined by (through `id`), and evaluate them, the registered numerals to casts: the map becomes a
lambda of real expressions in the value of its variable, the point a real number, `±∞` or its
filter `atTop`/`atBot`. -/
meta def unfoldLimit : TacticM Unit := do
  evalTactic (← `(tactic| try simp only [id_eq, CasCatalogue.Algebra.RealLimits.approachInfinity,
    CasCatalogue.Algebra.RealLimits.approach]))
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let expanded ← deltaExpand target fun n => n.getRoot == `CasCatalogue
  replaceMainGoal [← goal.replaceTargetDefEq expanded]
  -- A numeral `k` of a registered ring is the image of `k` under the initial ring map `ℤ → R`
  -- (`NamedRings.ringNumeral`), however that map is presented (`⇑f`, `f.toFun`, through its
  -- monoid and unit homomorphisms): it is the cast `(k : R)` (`eq_intCast`). A composite of
  -- registered maps is applied map by map (`ConcreteCategory.comp_apply`), so that a value carried
  -- into `ℝˣ` and back is the value (`Units.val_mk0`).
  evalTactic (← `(tactic| try simp only [id_eq, TypeCat.ofHom_apply, ConcreteCategory.comp_apply,
    RingHom.toFun_eq_coe,
    OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, eq_intCast,
    Int.cast_natCast, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero,
    Int.cast_one, Units.val_inv_eq_inv_val, Units.val_mk0, one_mul, mul_one,
    CasCatalogue.Algebra.RealLimits.comap_nhdsNE_top,
    CasCatalogue.Algebra.RealLimits.comap_nhdsNE_bot]))
  collapseUnits
  evalTactic (← `(tactic| try simp only [one_mul, mul_one]))

/-- The goal `Tendsto f (comap ι G) (𝓝 L)` for a map `f = fun t => e[ι t]` on a subobject
`ι : D ↪ ℝ` becomes `Tendsto (fun s => e[s]) G (𝓝 L)`: every occurrence of the variable in `e`
is through `ι` (`Subtype.val`, `Units.val`), and `e` is a real expression in `ι t`. -/
meta def restrictToLine : TacticM Unit := do
  let target ← whnfR (← instantiateMVars (← getMainTarget))
  unless target.isAppOf ``Filter.Tendsto do throwError "not a statement of convergence"
  let f := target.getAppArgs[2]!
  let F ← whnfR target.getAppArgs[3]!
  unless F.isAppOf ``Filter.comap do throwError "the filter is not traced on a subobject of ℝ"
  let ι := F.getAppArgs[2]!
  let f ← if f.isLambda then pure f else etaExpand f
  let g ← lambdaTelescope f fun xs body => do
    let some t := xs[0]? | throwError "not a map"
    let body ← kabstract body.headBeta (mkApp ι t)
    if body.containsFVar t.fvarId! then
      throwError "the map uses its variable other than as a real number"
    let s := mkBVar 0
    return Expr.lam `s (mkConst ``Real) (body.instantiate1 s) .default
  let gStx ← Term.exprToSyntax g
  evalTactic (← `(tactic| refine Filter.Tendsto.comp (g := $gStx) ?_ Filter.tendsto_comap))

/-- Close `Tendsto g G (𝓝 L)`, `G` the filter `𝓝[≠] x`, `atTop` or `atBot` of `ℝ`, assigning `L`:

* a standard limit: `sin t / t → 1` at `0` (`tendsto_sin_div_self`), `1/t → 0` at `±∞`
  (`tendsto_inv_atTop_zero`, `tendsto_inv_atBot_zero`);
* at `x ∈ ℝ`, a map continuous at `x` tends to its value (`ContinuousAt.tendsto`), continuity
  being composed along the structure of `g` (Mathlib `fun_prop`), with denominators nonzero at
  `x` by evaluation;
* a constant tends to itself;
* sums, differences, negatives and products of convergent maps converge to the sum, … of the
  limits (`Filter.Tendsto.add`, …).

`fuel` bounds the depth of `g` that is read. -/
meta def limitCases : Nat → TacticM Unit
  | 0 => throwError "the map is not established to converge"
  | fuel + 1 =>
    -- After a rule for `+`, `-`, `·`, `-·`: establish the convergence of each operand; the limits
    -- of the operands are assigned as they are established.
    let operands : TacticM Unit := do
      let goals ← getGoals
      for g in goals do
        unless ← g.isAssigned do
          if (← instantiateMVars (← g.getType)).headBeta.isAppOf ``Filter.Tendsto then
            setGoals [g]
            limitCases fuel
      setGoals (← goals.filterM fun g => return !(← g.isAssigned))
    CasCatalogue.Evidence.closeByFirst m!"the map is not established to converge"
      [do evalTactic (← `(tactic| with_reducible_and_instances
            exact CasCatalogue.Algebra.RealLimits.tendsto_sin_div_self)),
       do evalTactic (← `(tactic| with_reducible_and_instances
            exact CasCatalogue.Algebra.RealLimits.tendsto_sin_mul_inv_self)),
       do evalTactic (← `(tactic| with_reducible_and_instances
            exact tendsto_inv_atTop_zero (𝕜 := ℝ))),
       do evalTactic (← `(tactic| with_reducible_and_instances
            exact tendsto_inv_atBot_zero (𝕜 := ℝ))),
       do evalTactic (← `(tactic| with_reducible_and_instances
            exact tendsto_const_nhds (X := ℝ))),
       do
        evalTactic (← `(tactic| with_reducible_and_instances
          refine Filter.Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds))
        evalTactic (← `(tactic| fun_prop (disch := (intros; (first | positivity | norm_num))))),
       do
        evalTactic (← `(tactic| with_reducible_and_instances apply Filter.Tendsto.add (M := ℝ)))
        operands,
       do
        evalTactic (← `(tactic| with_reducible_and_instances apply Filter.Tendsto.sub (G := ℝ)))
        operands,
       do
        evalTactic (← `(tactic| with_reducible_and_instances apply Filter.Tendsto.mul (M := ℝ)))
        operands,
       do
        evalTactic (← `(tactic| with_reducible_and_instances apply Filter.Tendsto.neg (G := ℝ)))
        operands]

/-- The evidence that a closed map converges at a closed point `a` of `ℝ̄`: the statement
`∃ L, Tendsto f (t → a) (𝓝 L)`. The map and the point are evaluated (`unfoldLimit`), the map is
read as a real expression in its variable on `ℝ` (`restrictToLine`), and its limit is established
by `limitCases`, which assigns `L`. It fails on a map it does not establish to converge
(`sin(1/t)` at `0`, `t` at `∞`). -/
meta def convergenceEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "convergent maps" do
    unfoldLimit
    -- The limit `L` is left to unification (a natural metavariable), assigned by `limitCases`.
    evalTactic (← `(tactic| apply Exists.intro))
    let goals ← getGoals
    let some convergence ← goals.findM? fun g => do
        return (← instantiateMVars (← g.getType)).headBeta.isAppOf ``Filter.Tendsto
      | throwError "no statement of convergence"
    setGoals [convergence]
    restrictToLine
    limitCases 8
    setGoals (← goals.filterM fun g => return !(← g.isAssigned))

end CasCatalogue.Algebra.RealLimits

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.extended_reals"⟩, category := CategoryId.sets, name := "ℝ̄"
    declaration := `CasCatalogue.Algebra.RealLimits.extendedReals }

normalized_registry .inclusion
  { id := ⟨"incl.sets.reals_extended_reals"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.reals"⟩, super := ⟨"obj.sets.extended_reals"⟩
    declaration := `CasCatalogue.Algebra.RealLimits.realsExtendedReals
    mono := `CasCatalogue.Algebra.RealLimits.realsExtendedReals_mono }

normalized_registry .object
  { id := ⟨"obj.sets.infinities"⟩, category := CategoryId.sets, name := "ℝ̄∖ℝ"
    declaration := `CasCatalogue.Algebra.RealLimits.infinities
    inclusion := some `CasCatalogue.Algebra.RealLimits.infinitiesInclusion }

normalized_registry .morphism
  { id := ⟨"mor.sets.infinity"⟩, category := CategoryId.sets, name := "∞"
    declaration := `CasCatalogue.Algebra.RealLimits.infinity }

normalized_registry .morphism
  { id := ⟨"mor.sets.neg_infinity"⟩, category := CategoryId.sets, name := "-∞"
    declaration := `CasCatalogue.Algebra.RealLimits.negInfinity }

normalized_registry .object
  { id := ⟨"obj.sets.punctured_line"⟩, category := CategoryId.sets, name := "ℝ∖{a}"
    declaration := `CasCatalogue.Algebra.RealLimits.puncturedLine
    inclusion := some `CasCatalogue.Algebra.RealLimits.puncturedInclusion }

normalized_registry .object
  { id := ⟨"obj.sets.convergent_maps"⟩, category := CategoryId.sets, name := "Convergent"
    declaration := `CasCatalogue.Algebra.RealLimits.convergentMaps
    admission := some `CasCatalogue.Algebra.RealLimits.admitConvergent
    evidence := some `CasCatalogue.Algebra.RealLimits.convergenceEvidence }

normalized_registry .object
  { id := ⟨"obj.sets.convergent_maps_at_infinity"⟩, category := CategoryId.sets
    name := "ConvergentAtInfinity"
    declaration := `CasCatalogue.Algebra.RealLimits.convergentMapsAtInfinity
    admission := some `CasCatalogue.Algebra.RealLimits.admitConvergentAtInfinity
    evidence := some `CasCatalogue.Algebra.RealLimits.convergenceEvidence }

normalized_registry .binder
  { id := ⟨"bind.sets.limit"⟩, category := CategoryId.sets, token := "lim"
    operation := `CasCatalogue.Algebra.RealLimits.limit
    domain := `CasCatalogue.Algebra.RealLimits.limitDomain }

normalized_registry .binder
  { id := ⟨"bind.sets.limit_at_infinity"⟩, category := CategoryId.sets, token := "lim"
    operation := `CasCatalogue.Algebra.RealLimits.limitAtInfinity
    domain := `CasCatalogue.Algebra.RealLimits.limitAtInfinityDomain }

end CasCatalogue
