/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public import LeanCategories.Catalogue.Semantics.Algebra.CommutativeMonoids
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.PSeries
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.CommutativeMonoids

@[expose] public section

/-!
# Series: sums of summable families (`∑_{n ∈ N} e`)

A family `f : N → Y` of elements of a commutative topological monoid is *summable* when its finite
partial sums `∑_{n ∈ s} f(n)`, over the finite subsets `s ⊆ N` directed by inclusion, converge
(Bourbaki, *General Topology*, III.5.1; Mathlib `HasSum`, `Summable`). Its sum `∑_{n ∈ N} f(n)`
(Mathlib `tsum`) is then the limit of the partial sums, unique when `Y` is Hausdorff. The sum is a
total map out of the summable families, `Σ(N, Y) → Y`, and that is the binder `∑_{n ∈ N} e`
(`lean-cas-dsl/specs/binders.md`): its argument is the index set `N`, and the bound variable
ranges over `N`. A family is in `Σ(N, Y)` only with the evidence that it is summable.

## The category of the codomain (LC-13)

The sum uses the addition, the zero and the topology of `Y`, and its uniqueness uses that `Y` is
Hausdorff, Bourbaki's setting (*General Topology*, III.5.1, for groups; Mathlib, for monoids).
So `Y` is an object of the category `HausdorffTopAddCommMon` of Hausdorff commutative topological
monoids, written additively: an additive commutative monoid with a Hausdorff topology in which
addition is continuous, and continuous additive monoid maps (Mathlib `ContinuousAdd`, `T2Space`,
`ContinuousAddMonoidHom`). Its structural functor to additive commutative monoids forgets the
topology. The topology is part of the object, never found by instance search on a carrier: the
set `R[[t]]` underlies several objects of the category (for `ℚ[[t]]`, the product topology of the
absolute value of `ℚ` sums the constants `n ↦ 2⁻ⁿ` to `2`, the `(t)`-adic one does not).

The binder has one row per object, since the set of values of the body does not determine the
topology: `ℝ` and `ℂ` with the topology of their absolute values (`realSeriesSum`,
`complexSeriesSum`), `R[[t]]` with its `(t)`-adic topology (`powerSeriesSum`).

## Formal power series

`R[[t]]` carries the `(t)`-adic topology: the product topology of the discrete topology on each
coefficient (Bourbaki, *Algebra II*, IV.4.2; Mathlib `PowerSeries.WithPiTopology` at the discrete
topology of `R`), in which a sequence converges when each coefficient is eventually constant. It
is the topology in which `Σ c(n) tⁿ` is the sum of its terms: `∑_{n ∈ ℕ} c(n) tⁿ = mk c`
(`tsum_C_mul_X_pow`). A family whose `t`-adic order tends to `∞` is summable
(`summable_of_tendsto_order`): each coefficient of its terms vanishes for all but finitely many
indices. In particular a family `n ↦ fₙ` with `tⁿ ∣ fₙ` is summable (`summable_of_X_pow_dvd`).

Mathlib leaves the topology of `R[[t]]` scoped, since `R` may carry its own; the `(t)`-adic one is
named here (`tAdic`), `R[[t]]` with it is the object `powerSeriesTAdic R`, and the sum of series in
`R[[t]]` is the series sum at that object (`powerSeriesSum`, `powerSeriesSum_eq`).

The coefficient parameter of `powerSeriesTAdic` and the power-series binder is
the chosen commutative ring `R : CommRingCat`, rather than a carrier with a
separately supplied ring instance. The generic Mathlib topology lemmas below
remain at their original typeclass generality; the catalogue construction
obtains that structure from its ring object, and fixes the discrete coefficient
topology explicitly.
-/

open CategoryTheory Filter Topology

namespace CasCatalogue

namespace CategoryId
def hausdorffTopologicalMonoids : CategoryId := ⟨"cat.hausdorff_topological_commutative_monoids"⟩
end CategoryId

namespace FunctorId
def hausdorffTopologicalMonoidsForget : FunctorId :=
  ⟨"fun.hausdorff_topological_commutative_monoids.additive_commutative_monoid"⟩
end FunctorId

end CasCatalogue

namespace CasCatalogue.Algebra.Series

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

universe u

/-- A Hausdorff commutative topological monoid, written additively: an additive commutative monoid
with a Hausdorff topology in which addition is continuous. -/
structure HausdorffTopAddCommMon : Type (u + 1) where
  /-- The Hausdorff commutative topological monoid on a carrier with that structure. -/
  of ::
  /-- The underlying set. -/
  carrier : Type u
  [isAddCommMonoid : AddCommMonoid carrier]
  [isTopologicalSpace : TopologicalSpace carrier]
  [isContinuousAdd : ContinuousAdd carrier]
  [isT2Space : T2Space carrier]

namespace HausdorffTopAddCommMon

instance : CoeSort HausdorffTopAddCommMon.{u} (Type u) := ⟨carrier⟩

attribute [instance] isAddCommMonoid isTopologicalSpace isContinuousAdd isT2Space

/-- The continuous additive monoid maps. -/
instance : Category HausdorffTopAddCommMon.{u} where
  Hom Y Z := ContinuousAddMonoidHom Y Z
  id Y := ContinuousAddMonoidHom.id Y
  comp f g := g.comp f
  id_comp _ := ContinuousAddMonoidHom.ext fun _ => rfl
  comp_id _ := ContinuousAddMonoidHom.ext fun _ => rfl
  assoc _ _ _ := ContinuousAddMonoidHom.ext fun _ => rfl

/-- The underlying additive commutative monoid: the topology is forgotten. -/
def forgetTopology : HausdorffTopAddCommMon.{u} ⥤ AddCommMonCat.{u} where
  obj Y := AddCommMonCat.of Y
  map f := AddCommMonCat.ofHom (ContinuousAddMonoidHom.toAddMonoidHom f)

end HausdorffTopAddCommMon

/-- The Hausdorff commutative topological monoids, as an object of the categories. -/
def HausdorffTopologicalMonoids : LeanCategories.ObjCat.{u + 1, u} :=
  Cat.of HausdorffTopAddCommMon.{u}

def HausdorffTopologicalMonoidsExpr : CategoryExpr :=
  .atom CategoryId.hausdorffTopologicalMonoids

noncomputable def hausdorffTopologicalMonoidsRealization :
    CategoryRealization HausdorffTopologicalMonoidsExpr HausdorffTopologicalMonoids.{u} := {}

/-- The underlying additive commutative monoid of a Hausdorff commutative topological monoid. -/
def hausdorffTopologicalMonoidsForget :
    HausdorffTopologicalMonoids.{u} ⟶
      CasCatalogue.Algebra.CommMonoids.AdditiveCommutativeMonoids.{u} :=
  HausdorffTopAddCommMon.forgetTopology.toCatHom

def HausdorffTopologicalMonoidsForgetExpr :
    FunctorExpr HausdorffTopologicalMonoidsExpr
      CasCatalogue.Algebra.CommMonoids.AdditiveCommutativeMonoidsExpr :=
  .atomic FunctorId.hausdorffTopologicalMonoidsForget

noncomputable def hausdorffTopologicalMonoidsForgetRealization :
    FunctorRealization HausdorffTopologicalMonoidsForgetExpr HausdorffTopologicalMonoids.{u}
      CasCatalogue.Algebra.CommMonoids.AdditiveCommutativeMonoids.{u}
      hausdorffTopologicalMonoidsForget.toFunctor :=
  { sourceRealization := hausdorffTopologicalMonoidsRealization
    targetRealization :=
      CasCatalogue.Algebra.CommMonoids.additiveCommutativeMonoidsRealization }

/-- A Hausdorff commutative topological monoid as a `HausdorffTopAddCommMon`. -/
abbrev asTopMonoid (Y : HausdorffTopologicalMonoids.{0}) : HausdorffTopAddCommMon.{0} := Y

/-- `ℝ`, with the topology of its absolute value. -/
noncomputable abbrev realsTop : HausdorffTopologicalMonoids.{0} := HausdorffTopAddCommMon.of ℝ

/-- `ℂ`, with the topology of its absolute value. -/
noncomputable abbrev complexesTop : HausdorffTopologicalMonoids.{0} := HausdorffTopAddCommMon.of ℂ

/-- A summable family `N → Y`. -/
structure SummableFamily (Y : HausdorffTopologicalMonoids.{0}) (N : Type) : Type where
  /-- The family. -/
  toFun : N → asTopMonoid Y
  /-- It is summable. -/
  summable : Summable toFun

/-- `Σ(N, Y)`, the summable families `N → Y`. -/
abbrev summableFamilies (Y : HausdorffTopologicalMonoids.{0}) (N : Type) : SetsCat.{0} :=
  SummableFamily Y N

/-- The family `f`, with the evidence that it is summable. -/
def admit (Y : HausdorffTopologicalMonoids.{0}) (N : Type) (f : N → asTopMonoid Y)
    (h : Summable f) : fin 1 ⟶ summableFamilies Y N :=
  TypeCat.ofHom fun _ => ⟨f, h⟩

/-- `f ↦ ∑_{n ∈ N} f(n)`, `Σ(N, Y) → Y`, in a Hausdorff commutative topological monoid `Y`
(Mathlib `tsum`). The sum is the limit of the partial sums of the admitted family, unique because
`Y` is Hausdorff (`HasSum.unique`). It is not itself a binder row: the set of values of the body
does not determine the object `Y` (`R[[t]]` underlies several), so each binder row of `∑_{n ∈ N}`
is this sum at one named object (`realSeriesSum`, `complexSeriesSum`, `powerSeriesSum`), and the
codomain of the body selects the row. -/
noncomputable def seriesSum (Y : HausdorffTopologicalMonoids.{0}) (N : Type) :
    summableFamilies Y N ⟶ (asTopMonoid Y : SetsCat.{0}) :=
  TypeCat.ofHom fun f => ∑' n, f.toFun n

/-- `f ↦ ∑_{n ∈ N} f(n)`, `Σ(N, ℝ) → ℝ`: the sum of real series, in the topology of the absolute
value of `ℝ`. The binder `∑_{n ∈ N} e` with values in `ℝ`; its argument is the index set `N`. -/
noncomputable def realSeriesSum (N : Type) :
    summableFamilies realsTop N ⟶ CasCatalogue.Algebra.NumberSystems.reals :=
  TypeCat.ofHom fun f => ∑' n, f.toFun n

/-- The bound variable of `∑_{n ∈ N}` with values in `ℝ` ranges over `N`. -/
abbrev realSeriesDomain (N : Type) : SetsCat.{0} := N

/-- The sum of real series is the series sum of `ℝ`. -/
theorem realSeriesSum_eq (N : Type) : realSeriesSum N = seriesSum realsTop N := rfl

/-- `f ↦ ∑_{n ∈ N} f(n)`, `Σ(N, ℂ) → ℂ`: the sum of complex series, in the topology of the
absolute value of `ℂ`. The binder `∑_{n ∈ N} e` with values in `ℂ`. -/
noncomputable def complexSeriesSum (N : Type) :
    summableFamilies complexesTop N ⟶ CasCatalogue.Algebra.NumberSystems.complexes :=
  TypeCat.ofHom fun f => ∑' n, f.toFun n

/-- The bound variable of `∑_{n ∈ N}` with values in `ℂ` ranges over `N`. -/
abbrev complexSeriesDomain (N : Type) : SetsCat.{0} := N

/-- The sum of complex series is the series sum of `ℂ`. -/
theorem complexSeriesSum_eq (N : Type) : complexSeriesSum N = seriesSum complexesTop N := rfl

/-- The series sum of an admitted family is a sum of it: the partial sums converge to it. -/
theorem hasSum_seriesSum (Y : HausdorffTopologicalMonoids.{0}) (N : Type)
    (f : summableFamilies Y N) :
    HasSum f.toFun (ConcreteCategory.hom (C := Type) (seriesSum Y N) f) :=
  f.summable.hasSum

/-- The series sum is the unique sum: any `y` to which the partial sums converge is it. -/
theorem seriesSum_eq_of_hasSum (Y : HausdorffTopologicalMonoids.{0}) (N : Type)
    (f : summableFamilies Y N) (y : asTopMonoid Y) (h : HasSum f.toFun y) :
    ConcreteCategory.hom (C := Type) (seriesSum Y N) f = y :=
  (hasSum_seriesSum Y N f).unique h

/-! ### `R[[t]]` with its `(t)`-adic topology -/

/-- The `(t)`-adic topology of `R[[t]]`: the product topology of the discrete topology on the
coefficients (Mathlib `PowerSeries.WithPiTopology` at `⊥`; Bourbaki, *Algebra II*, IV.4.2). -/
@[reducible] def tAdic (R : Type) [CommRing R] : TopologicalSpace (PowerSeries R) :=
  @PowerSeries.WithPiTopology.instTopologicalSpace R ⊥

section TAdic

attribute [local instance] tAdic

/-- The `(t)`-adic topology is Hausdorff: the coefficients are discrete. -/
theorem tAdic_t2Space (R : Type) [CommRing R] : T2Space (PowerSeries R) :=
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  PowerSeries.WithPiTopology.instT2Space R

/-- In the `(t)`-adic topology a family has sum `g` iff, for each `d`, the `d`-th coefficients of
its terms have sum the `d`-th coefficient of `g` in the discrete `R`
(Mathlib `PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff`). -/
theorem hasSum_iff_hasSum_coeff {R : Type} [CommRing R] {N : Type} {f : N → PowerSeries R}
    {g : PowerSeries R} :
    HasSum f g ↔
      letI : TopologicalSpace R := ⊥
      ∀ d, HasSum (fun i ↦ PowerSeries.coeff d (f i)) (PowerSeries.coeff d g) :=
  letI : TopologicalSpace R := ⊥
  PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff R

/-- **A family whose `t`-adic order tends to `∞` is summable.** If for every `d` all but finitely
many terms of `f` have order `> d`, then for every `d` all but finitely many terms have vanishing
`d`-th coefficient (`PowerSeries.coeff_of_lt_order`), so each coefficient family has finite
support and is summable in the discrete `R`, and `f` is summable in the product topology
(`PowerSeries.WithPiTopology.summable_iff_summable_coeff`). The index set is arbitrary, ordered by
the cofinite filter; on `ℕ` this is Mathlib's
`PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top`. -/
theorem summable_of_tendsto_order {R : Type} [CommRing R] {N : Type} {f : N → PowerSeries R}
    (h : Tendsto (fun i ↦ (f i).order) cofinite (𝓝 ⊤)) : Summable f := by
  let _ : TopologicalSpace R := ⊥
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  rw [ENat.tendsto_nhds_top_iff_natCast_lt] at h
  exact (Filter.eventually_cofinite.mp (h d)).subset fun i hi hlt =>
    hi (PowerSeries.coeff_of_lt_order d hlt)

/-- A family `n ↦ fₙ` with `tⁿ ∣ fₙ` is summable in the `(t)`-adic topology: the order of `fₙ` is
at least `n`, which tends to `∞` (`summable_of_tendsto_order`). The terms `c(n) tⁿ` of a power
series are such a family. -/
theorem summable_of_X_pow_dvd {R : Type} [CommRing R] {f : ℕ → PowerSeries R}
    (h : ∀ n, PowerSeries.X ^ n ∣ f n) : Summable f := by
  refine summable_of_tendsto_order ?_
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro d
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨d + 1, fun n hn => ?_⟩
  have hle : (n : ℕ∞) ≤ (f n).order := by
    refine PowerSeries.nat_le_order _ _ fun i hi => ?_
    exact PowerSeries.X_pow_dvd_iff.mp (h n) i hi
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_of_succ_le hn) hle

/-- `∑_{n ∈ ℕ} c(n) tⁿ = Σ c(n) tⁿ`: the terms `c(n) tⁿ` have sum the series with coefficients
`c` in the `(t)`-adic topology, since the `d`-th coefficient of `c(n) tⁿ` is `c(d)` at `n = d`
and `0` elsewhere (`PowerSeries.coeff_C_mul_X_pow`). -/
theorem hasSum_C_mul_X_pow {R : Type} [CommRing R] (c : ℕ → R) :
    HasSum (fun n ↦ PowerSeries.C (c n) * PowerSeries.X ^ n) (PowerSeries.mk c) := by
  rw [hasSum_iff_hasSum_coeff]
  intro d
  simp only [PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_mk]
  have hterm : (fun n ↦ if d = n then c n else 0) = fun n ↦ if n = d then c d else 0 := by
    funext n
    by_cases hnd : n = d
    · subst hnd; simp
    · simp [hnd, Ne.symm hnd]
  rw [hterm]
  exact @hasSum_ite_eq R ℕ _ ⊥ d _ (c d) (SummationFilter.unconditional ℕ) _

/-- **The identification `∑_{n ∈ ℕ} c(n) tⁿ = mk c`** in `R[[t]]` with the `(t)`-adic topology:
the coefficient of `tᵈ` of the series sum is `c(d)`. -/
theorem tsum_C_mul_X_pow {R : Type} [CommRing R] (c : ℕ → R) :
    ∑' n, PowerSeries.C (c n) * PowerSeries.X ^ n = PowerSeries.mk c :=
  haveI := tAdic_t2Space R
  (hasSum_C_mul_X_pow c).tsum_eq

/-- The same identification with the terms written `c(n) • tⁿ`. -/
theorem tsum_smul_X_pow {R : Type} [CommRing R] (c : ℕ → R) :
    ∑' n, c n • PowerSeries.X ^ n = PowerSeries.mk c := by
  simp only [PowerSeries.smul_eq_C_mul]
  exact tsum_C_mul_X_pow c

/-- Addition of `R[[t]]` is continuous in the `(t)`-adic topology: `R[[t]]` is a topological ring
over the discrete `R` (Mathlib `PowerSeries.WithPiTopology.instIsTopologicalRing`). -/
theorem tAdic_continuousAdd (R : Type) [CommRing R] : ContinuousAdd (PowerSeries R) :=
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  haveI := PowerSeries.WithPiTopology.instIsTopologicalRing (R := R)
  inferInstance

/-- `R[[t]]` with its `(t)`-adic topology, a Hausdorff commutative topological monoid. -/
noncomputable abbrev powerSeriesTAdic (R : CommRingCat.{0}) : HausdorffTopologicalMonoids.{0} :=
  @HausdorffTopAddCommMon.of (PowerSeries R) _ (tAdic R) (tAdic_continuousAdd R) (tAdic_t2Space R)

/-- The sum of series in `R[[t]]`: `f ↦ ∑_{n ∈ N} f(n)`, the series sum `seriesSum` at the
object `powerSeriesTAdic R` (`powerSeriesSum_eq`). The binder `∑_{n ∈ N} e` with values in
`R[[t]]`: its argument is the index set `N`, and `R` is read off the body's codomain `R[[t]]`. -/
noncomputable def powerSeriesSum (R : CommRingCat.{0}) (N : Type) :
    summableFamilies (powerSeriesTAdic R) N ⟶ CasCatalogue.Algebra.Calculus.powerSeries R :=
  TypeCat.ofHom fun f => ∑' n, f.toFun n

/-- The bound variable of `∑_{n ∈ N}` with values in `R[[t]]` ranges over `N`. -/
abbrev powerSeriesSumDomain (_ : CommRingCat.{0}) (N : Type) : SetsCat.{0} := N

/-- The sum of series in `R[[t]]` is the series sum of the Hausdorff monoid `R[[t]]` with its
`(t)`-adic topology. -/
theorem powerSeriesSum_eq (R : CommRingCat.{0}) (N : Type) :
    powerSeriesSum R N = seriesSum (powerSeriesTAdic R) N :=
  rfl

/-- `∑_{n ∈ ℕ} c(n) tⁿ` at the admitted family `n ↦ C(c(n)) tⁿ` is the series `mk c`. -/
theorem powerSeriesSum_C_mul_X_pow (R : CommRingCat.{0}) (c : ℕ → R)
    (h : Summable fun n ↦ PowerSeries.C (c n) * PowerSeries.X ^ n) :
    ConcreteCategory.hom (C := Type) (powerSeriesSum R naturals)
      ⟨fun n ↦ PowerSeries.C (c n) * PowerSeries.X ^ n, h⟩ = PowerSeries.mk c :=
  tsum_C_mul_X_pow c

end TAdic

/-! ### The evidence of summability -/

open Lean Meta Elab Tactic

/-- Unfold the catalogue's operations in the main goal to the Mathlib terms they are defined by,
and apply them (`TypeCat.ofHom_apply`): the family becomes a lambda of ring expressions. -/
meta def unfoldCatalogue : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let expanded ← deltaExpand target fun n => n.getRoot == `CasCatalogue
  replaceMainGoal [← goal.replaceTargetDefEq expanded]
  evalTactic (← `(tactic| try simp only [id_eq, TypeCat.ofHom_apply, ConcreteCategory.comp_apply,
    Units.val_inv_eq_inv_val,
    Units.val_mk0, one_mul, mul_one]))

/-- Close `tⁿ ∣ e`: `e` is a multiple of `tⁿ` or a power `tᵐ`, `m ≥ n`, or a sum, difference,
negative or multiple of such, by the divisibility rules of a commutative ring (`dvd_mul_left`,
`pow_dvd_pow`, `dvd_add`, `Dvd.dvd.mul_left`, …); `fuel` bounds the depth of `e` that is read. -/
meta def dvdCases : Nat → TacticM Unit
  | 0 => throwError "the term is not established to be a multiple of tⁿ"
  | fuel + 1 =>
    CasCatalogue.Evidence.closeByFirst m!"the term is not established to be a multiple of tⁿ"
      [do evalTactic (← `(tactic| with_reducible_and_instances exact dvd_mul_left _ _)),
       do evalTactic (← `(tactic| with_reducible_and_instances exact dvd_mul_right _ _)),
       do evalTactic (← `(tactic| with_reducible_and_instances exact dvd_rfl)),
       do evalTactic (← `(tactic| with_reducible_and_instances exact dvd_zero _)),
       do evalTactic (← `(tactic| (with_reducible_and_instances refine pow_dvd_pow _ ?_); omega)),
       do
        evalTactic (← `(tactic| with_reducible_and_instances refine dvd_add ?_ ?_))
        for g in ← getGoals do
          setGoals [g]
          dvdCases fuel,
       do
        evalTactic (← `(tactic| with_reducible_and_instances refine dvd_sub ?_ ?_))
        for g in ← getGoals do
          setGoals [g]
          dvdCases fuel,
       do
        evalTactic (← `(tactic| with_reducible_and_instances refine (dvd_neg).mpr ?_))
        dvdCases fuel,
       do
        evalTactic (← `(tactic| with_reducible_and_instances refine Dvd.dvd.mul_left ?_ _))
        dvdCases fuel,
       do
        evalTactic (← `(tactic| with_reducible_and_instances refine Dvd.dvd.mul_right ?_ _))
        dvdCases fuel]

/-- The evidence that a closed family is summable, by the topology of its values:

* in `R[[t]]` with the `(t)`-adic topology, a family `n ↦ fₙ` over `ℕ` with `tⁿ ∣ fₙ`
  (`summable_of_X_pow_dvd`): the terms `c(n) tⁿ` of a power series, and sums and multiples of
  them;
* in `ℝ`, the geometric series `(1/2)ⁿ`, `rⁿ` with `0 ≤ r < 1` (`summable_geometric_of_lt_one`), and
  the `p`-series `1/nᵖ`, `p > 1` (`Real.summable_one_div_nat_pow`, `Real.summable_nat_pow_inv`).

It fails on a family it does not establish to be summable (`n ↦ 1` in `ℝ`, `n ↦ t⁰` in
`R[[t]]`). -/
meta def summableEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "Σ(N, Y)" do
    unfoldCatalogue
    -- The values: `Summable (α := Y) f` is read at the monoid `Y` of its values.
    let target ← whnfR (← getMainTarget)
    unless target.isAppOf ``Summable do throwError "not a statement of summability"
    let values ← whnfR target.getAppArgs[0]!
    -- `R[[t]]` is `MvPowerSeries Unit R` by definition (Mathlib `PowerSeries`).
    if values.isAppOf ``PowerSeries || values.isAppOf ``MvPowerSeries then
      evalTactic (← `(tactic| refine CasCatalogue.Algebra.Series.summable_of_X_pow_dvd ?_))
      evalTactic (← `(tactic| intro n))
      evalTactic (← `(tactic| try simp only [PowerSeries.smul_eq_C_mul, nsmul_eq_mul,
        zsmul_eq_mul, PowerSeries.monomial_eq_C_mul_X_pow]))
      dvdCases 8
    else if values.isConstOf ``Real then
      CasCatalogue.Evidence.closeByFirst m!"the real family is not established to be summable"
        [do evalTactic (← `(tactic| with_reducible_and_instances exact summable_geometric_two)),
         do evalTactic (← `(tactic|
            (with_reducible_and_instances refine summable_geometric_of_lt_one ?_ ?_) <;> norm_num)),
         do evalTactic (← `(tactic|
            (with_reducible_and_instances refine Real.summable_one_div_nat_pow.mpr ?_); norm_num)),
         do evalTactic (← `(tactic|
            (with_reducible_and_instances refine Real.summable_nat_pow_inv.mpr ?_); norm_num))]
    else
      throwError "no summability evidence for families with values in{indentExpr values}"

end CasCatalogue.Algebra.Series

namespace CasCatalogue

normalized_registry .category
  { id := CategoryId.hausdorffTopologicalMonoids, name := "HausdorffTopologicalMonoids"
    declaration := `CasCatalogue.Algebra.Series.HausdorffTopologicalMonoids
    expression := Algebra.Series.HausdorffTopologicalMonoidsExpr
    realization := `CasCatalogue.Algebra.Series.hausdorffTopologicalMonoidsRealization }

normalized_registry .functor
  { id := FunctorId.hausdorffTopologicalMonoidsForget
    source := Algebra.Series.HausdorffTopologicalMonoidsExpr
    target := Algebra.CommMonoids.AdditiveCommutativeMonoidsExpr
    declaration := `CasCatalogue.Algebra.Series.hausdorffTopologicalMonoidsForget
    realization := `CasCatalogue.Algebra.Series.hausdorffTopologicalMonoidsForgetRealization
    expression := Algebra.Series.HausdorffTopologicalMonoidsForgetExpr
    structural := true }

normalized_registry .object
  { id := ⟨"obj.sets.summable_families"⟩, category := CategoryId.sets, name := "Summable"
    declaration := `CasCatalogue.Algebra.Series.summableFamilies
    admission := some `CasCatalogue.Algebra.Series.admit
    evidence := some `CasCatalogue.Algebra.Series.summableEvidence }

normalized_registry .binder
  { id := ⟨"bind.sets.real_series"⟩, category := CategoryId.sets, token := "∑"
    operation := `CasCatalogue.Algebra.Series.realSeriesSum
    domain := `CasCatalogue.Algebra.Series.realSeriesDomain }

normalized_registry .binder
  { id := ⟨"bind.sets.complex_series"⟩, category := CategoryId.sets, token := "∑"
    operation := `CasCatalogue.Algebra.Series.complexSeriesSum
    domain := `CasCatalogue.Algebra.Series.complexSeriesDomain }

normalized_registry .binder
  { id := ⟨"bind.sets.power_series_sum"⟩, category := CategoryId.sets, token := "∑"
    operation := `CasCatalogue.Algebra.Series.powerSeriesSum
    domain := `CasCatalogue.Algebra.Series.powerSeriesSumDomain }

end CasCatalogue
