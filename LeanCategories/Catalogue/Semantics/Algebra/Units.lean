/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence

@[expose] public section

/-!
# Units (LC-14: inverses exist on units, not on a monoid)

A monoid `M` has no inverses in general; its units `Mˣ` (Mathlib `Units`, the units functor
`Mon → Grp`) form a group, and `⁻¹` is part of that group's structure: an operation on `Mˣ`, never
on `M`. The endomorphisms `Matₙ(K) = End(Kⁿ)` form a monoid; their units are the automorphisms
`GLₙ(K) = Aut(Kⁿ) = Matₙ(K)ˣ`; the units of a field `K` are `K^× = K ∖ {0}`.

* `Mˣ ↪ M` (`Units.val`) is a monomorphism: a unit is an element of `M`.
* An element of `Mˣ` is a pair `(x, y)` of elements of `M` with `x y = y x = 1` (Mathlib `Units`).
  An element `x ∈ M` is admitted into `Mˣ` with the evidence `Invertible x`: its inverse `⅟x`
  together with `⅟x · x = x · ⅟x = 1` (Mathlib `Invertible`, `unitOfInvertible`). Without it, `x`
  is not an element of `Mˣ`, and `x⁻¹` is not a term.
* The admission keeps the inverse as data, so the inverse of an admitted unit is the evidence's
  `⅟x` and computes wherever `⅟x` does (`(3 : ℚ)⁻¹`, `2⁻¹ ∈ ℤ/5`). The proposition `IsUnit x`
  says only that some inverse exists: a unit recovered from it (`IsUnit.unit`) has an inverse
  chosen by `Classical.choose`, which does not reduce.
* `Invertible x` is a subsingleton (`Invertible.subsingleton`: in a monoid, `y x = 1 = x z` gives
  `y = y x z = z`), so the admitted unit depends on `x` alone, as membership does, and
  `Nonempty (Invertible x) ↔ IsUnit x` (`isUnit_iff_nonempty_invertible`).
* `⁻¹ : Mˣ → Mˣ`, and division `M × Mˣ → M`, `(a, u) ↦ a u⁻¹`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.Units

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- `Mˣ`. -/
abbrev units (M : Type) [Monoid M] : SetsCat.{0} := Mˣ

/-- `Mˣ ↪ M`. -/
def inclusion (M : Type) [Monoid M] : units M ⟶ (M : SetsCat.{0}) := TypeCat.ofHom Units.val

/-- `u ↦ u⁻¹`, the inverse of the group `Mˣ`. -/
def inverse (M : Type) [Monoid M] : units M ⟶ units M := TypeCat.ofHom fun u => u⁻¹

/-- `(a, u) ↦ a u⁻¹`. -/
def divide (M : Type) [Monoid M] : (M × units M : SetsCat.{0}) ⟶ (M : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 * ↑(p.2⁻¹)

/-- The unit `x`, with its inverse: the evidence `h : Invertible x` is the inverse `⅟x` with
`⅟x · x = x · ⅟x = 1`, and the unit is the pair `(x, ⅟x)` (Mathlib `unitOfInvertible`). -/
def admit (M : Type) [Monoid M] (x : M) (h : Invertible x) : fin 1 ⟶ units M :=
  TypeCat.ofHom fun _ => @unitOfInvertible M _ x h

/-- The admitted unit is `x`: `1 → Mˣ ↪ M` is the element `x`. Stated with the composite
applied map by map, the simp-normal form (`CategoryTheory.types_comp_apply`). -/
@[simp] theorem admit_inclusion (M : Type) [Monoid M] (x : M) (h : Invertible x) (p : fin 1) :
    ConcreteCategory.hom (C := Type) (inclusion M)
        (ConcreteCategory.hom (C := Type) (admit M x h) p) = x :=
  rfl

/-- The inverse of the admitted unit is the evidence's inverse `⅟x`. -/
@[simp] theorem admit_inverse_inclusion (M : Type) [Monoid M] (x : M) (h : Invertible x)
    (p : fin 1) :
    ConcreteCategory.hom (C := Type) (inclusion M)
        (ConcreteCategory.hom (C := Type) (inverse M)
          (ConcreteCategory.hom (C := Type) (admit M x h) p)) = h.invOf :=
  rfl

/-- In `ℤ` a unit is its own inverse: `u · u = 1` for `u = ±1` (Mathlib `Int.isUnit_mul_self`). -/
@[instance_reducible] def invertibleOfIsUnitInt {u : ℤ} (h : IsUnit u) : Invertible u :=
  ⟨u, Int.isUnit_mul_self h, Int.isUnit_mul_self h⟩

/-- The only unit of `ℕ` is `1` (Mathlib `Nat.isUnit_iff`), its own inverse. -/
@[instance_reducible] def invertibleOfIsUnitNat {n : ℕ} (h : IsUnit n) : Invertible n :=
  ⟨1, by simp [Nat.isUnit_iff.mp h], by simp [Nat.isUnit_iff.mp h]⟩

/-- In `ℤ/n` the inverse of a unit `a` is `a⁻¹`, the Bézout coefficient of `a` modulo `n` computed
by the extended Euclidean algorithm (Mathlib `ZMod.inv`, `ZMod.inv_mul_of_unit`,
`ZMod.mul_inv_of_unit`). -/
@[instance_reducible] def invertibleOfIsUnitZMod {n : ℕ} {a : ZMod n} (h : IsUnit a) :
    Invertible a :=
  ⟨a⁻¹, ZMod.inv_mul_of_unit a h, ZMod.mul_inv_of_unit a h⟩

/-- In `ℤ/n` with `n ≠ 0`, `x` is a unit exactly when its representative `x.val ∈ [0, n)` is
coprime to `n` (Mathlib `ZMod.isUnit_iff_coprime`, stated there for the image of a natural
number). -/
theorem zmod_isUnit_iff_coprime_val {n : ℕ} [NeZero n] (x : ZMod n) :
    IsUnit x ↔ x.val.Coprime n := by
  rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]

open Lean Elab Tactic in
/-- The evidence of a closed arithmetic fact in a ring — that a closed element is nonzero, equal
to or ordered against another: the elements are evaluated (numerals, ring and field operations,
`re`/`im` of complex numbers, arithmetic of `ℤ/n` by computation), and a positive real expression
(`π`, `√a`, `exp a`) is nonzero because it is positive. -/
meta def closedArithmeticEvidence : TacticM Unit :=
  CasCatalogue.Evidence.closeByFirst m!"the closed arithmetic fact is not established"
    [do evalTactic (← `(tactic| norm_num)),
     do evalTactic (← `(tactic| positivity)),
     do evalTactic (← `(tactic| norm_num [Complex.ext_iff])),
     do evalTactic (← `(tactic| decide))]

open Lean Meta Elab Tactic in
/-- Evaluate the catalogue's numerals in the main goal. The numeral `k` of a ring or semiring `R`
is the image of `k` under the map out of the initial object, `ℤ → R` or `ℕ → R`
(`NamedRings.ringNumeral`, `Semirings.semiringNumeral`, LC-15), an element of the underlying set
of the object `RingCat.of R` of its category, which is `R` (the identifications of the named rings
with their sets are identities). The catalogue's declarations are unfolded, the underlying set of
`RingCat.of R` is read as `R`, and the image of `k` is rewritten to the cast `(k : R)`
(`eq_intCast`, `eq_natCast`), a numeral of `R` that arithmetic, reduction modulo the
characteristic and degree computation read. -/
meta def evaluateNumerals : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let expanded ← deltaExpand target fun n => n.getRoot == `CasCatalogue
  let carriers := [``RingCat.carrier, ``SemiRingCat.carrier, ``CommRingCat.carrier,
    ``CommSemiRingCat.carrier]
  let read ← Meta.transform expanded (post := fun e => do
    if carriers.any (e.isAppOfArity · 1) then return .done (← whnfR e)
    return .continue)
  replaceMainGoal [← goal.replaceTargetDefEq read]
  evalTactic (← `(tactic| try simp only [TypeCat.ofHom_apply, ConcreteCategory.comp_apply,
    eq_intCast, eq_natCast, Int.cast_natCast, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Int.cast_ofNat, Int.cast_zero, Int.cast_one]))

open Lean Elab Tactic in
/-- Expand the determinants of matrices of closed entries in the main goal along their first row
(`Matrix.det_succ_row_zero`), down to the ring's arithmetic. -/
meta def expandDeterminant : TacticM Unit := do
  evalTactic (← `(tactic| try simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
    Fin.zero_succAbove, Fin.succAbove_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.det_unique, Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton,
    Fin.val_zero, Fin.val_succ, Matrix.of_apply, Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.det_isEmpty, Matrix.det_one, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, Fin.prod_univ_succ, Fin.prod_univ_zero]))

open Lean Meta Elab Tactic in
/-- The modulus `n` when the monoid of the main goal `IsUnit x` or `Invertible x` is `ℤ/n`.

The case analysis is by the structure of the monoid, so the modulus is read from the goal's
carrier, never from the element: the element's own type need not name `ℤ/n` (the numeral `k` of
the ring `ℤ/n` lies in the underlying set of `RingCat.of (ZMod n)`; a Lean term may also reduce to
`⟨k, _⟩ : Fin n`, `ZMod n` being `Fin n` by definition for `n ≠ 0`). -/
meta def zmodModulus : TacticM Term := do
  let some carrier := (← getMainTarget).consumeMData.getAppArgs[0]?
    | throwError "not a statement about an element of a monoid"
  let carrier ← whnfR carrier
  unless carrier.isAppOfArity ``ZMod 1 do throwError "the monoid is not ℤ/n"
  Term.exprToSyntax carrier.appArg!

open Lean Elab Tactic in
/-- The units of the monoids of closed values, by the structure of the monoid `M`:

* every element of a group is a unit (`Mˣ`, `GLₙ(K)`, permutations);
* a square matrix over a commutative ring is a unit iff its determinant is
  (`Matrix.isUnit_iff_isUnit_det`); the determinant of a matrix of closed entries is expanded
  along its first row (`Matrix.det_succ_row_zero`) and its units are those of the ring;
* in a division ring (`ℚ`, `ℝ`, `ℂ`) the units are the nonzero elements (`isUnit_iff_ne_zero`);
* the units of `ℤ` are `±1` (`Int.isUnit_iff`), of `ℕ` only `1` (`Nat.isUnit_iff`);
* the units of `ℤ/n`, `n ≠ 0`, are the classes coprime to `n` (`zmod_isUnit_iff_coprime_val`),
  the modulus read from the monoid (`zmodModulus`), however the class is written;
* in any monoid, `1`, a product of units, a power of a unit and the negative of a unit are units.

It fails on an element that is not a unit (`2 ∈ ℤ`, `0 ∈ ℚ`, a singular matrix). -/
meta partial def isUnitEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "Units" isUnitCases
where
  /-- The cases above, tried in turn on the main goal `IsUnit x`. -/
  isUnitCases : TacticM Unit :=
  CasCatalogue.Evidence.closeByFirst m!"the value is not established to be a unit"
    [do evalTactic (← `(tactic| exact Group.isUnit _)),
     do evalTactic (← `(tactic| exact isUnit_one)),
     do evalTactic (← `(tactic| exact Units.isUnit _)),
     do
      evalTactic (← `(tactic| rw [Matrix.isUnit_iff_isUnit_det]))
      expandDeterminant
      isUnitCases,
     do
      evalTactic (← `(tactic| rw [isUnit_iff_ne_zero]))
      closedArithmeticEvidence,
     do
      evalTactic (← `(tactic| rw [Int.isUnit_iff]))
      closedArithmeticEvidence,
     do
      evalTactic (← `(tactic| rw [Nat.isUnit_iff]))
      closedArithmeticEvidence,
     do
      -- Applied at the modulus of the goal's monoid, not rewritten: the element's type need not
      -- name `ZMod n`, and matches `x : ZMod n` only once `n` is known (`zmodModulus`).
      let n ← zmodModulus
      evalTactic (← `(tactic|
        refine (@CasCatalogue.Algebra.Units.zmod_isUnit_iff_coprime_val $n _ _).mpr ?_))
      CasCatalogue.Evidence.closeByFirst m!"not coprime to the modulus"
        [do evalTactic (← `(tactic| decide)),
         do evalTactic (← `(tactic| norm_num [Nat.coprime_iff_gcd_eq_one, ZMod.val]))],
     do
      let x := (← getMainTarget).consumeMData.appArg!
      if x.isAppOfArity ``HMul.hMul 6 then
        evalTactic (← `(tactic| refine IsUnit.mul ?_ ?_))
      else if x.isAppOfArity ``HPow.hPow 6 then
        evalTactic (← `(tactic| refine IsUnit.pow _ ?_))
      else if x.isAppOfArity ``Neg.neg 3 then
        evalTactic (← `(tactic| refine IsUnit.neg ?_))
      else
        throwError "not a product, power or negative of units"
      for goal in ← getGoals do
        setGoals [goal]
        isUnitCases]

open Lean Elab Tactic in
/-- The evidence of the admission into `Mˣ`: the inverse of a closed `x`, `Invertible x`, by the
structure of the monoid `M`. The inverse is the one the structure computes, and only the
equations `⅟x · x = x · ⅟x = 1` are proved (by `isUnitEvidence`, the inverse being unique):

* in a group, `x⁻¹` (`invertibleOfGroup`); for `1`, `1` (`invertibleOne`); for a unit `u`, `u⁻¹`
  (`Units.invertible`);
* for a square matrix `A` over a commutative ring, `(det A)⁻¹ · adj A`, from the inverse of its
  determinant (`Matrix.invertibleOfDetInvertible`, Cramer's rule);
* in a division ring (`ℚ`, `ℝ`, `ℂ`), `x⁻¹` for `x ≠ 0` (`invertibleOfNonzero`);
* in `ℤ`, `u⁻¹ = u` for `u = ±1`; in `ℕ`, `1⁻¹ = 1`;
* in `ℤ/n`, `a⁻¹` by the extended Euclidean algorithm (`ZMod.inv`);
* the inverse of a product, a power, a negative of units: `⅟b · ⅟a`, `(⅟a)ⁿ`, `-⅟a`
  (`invertibleMul`, `invertiblePow`, `invertibleNeg`).

It fails on an element that is not a unit (`2 ∈ ℤ`, `0 ∈ ℚ`, a singular matrix). -/
meta partial def invertibleEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "Units" invertibleCases
where
  /-- `IsUnit x` for the element `x` of a ring, its determinants expanded first. -/
  isUnitOfElement : TacticM Unit := do
    expandDeterminant
    isUnitEvidence.isUnitCases
  /-- The cases above, tried in turn on the main goal `Invertible x`. -/
  invertibleCases : TacticM Unit :=
  CasCatalogue.Evidence.closeByFirst m!"the value is not established to be a unit"
    [do evalTactic (← `(tactic| exact invertibleOfGroup _)),
     do evalTactic (← `(tactic| exact invertibleOne)),
     do evalTactic (← `(tactic| exact Units.invertible _)),
     do
      evalTactic (← `(tactic| refine @Matrix.invertibleOfDetInvertible _ _ _ _ _ _ ?_))
      invertibleCases,
     do
      evalTactic (← `(tactic| refine invertibleOfNonzero (isUnit_iff_ne_zero.mp ?_)))
      isUnitOfElement,
     do
      evalTactic (← `(tactic| refine CasCatalogue.Algebra.Units.invertibleOfIsUnitInt ?_))
      isUnitOfElement,
     do
      evalTactic (← `(tactic| refine CasCatalogue.Algebra.Units.invertibleOfIsUnitNat ?_))
      isUnitOfElement,
     do
      let n ← zmodModulus
      evalTactic (← `(tactic|
        refine @CasCatalogue.Algebra.Units.invertibleOfIsUnitZMod $n _ ?_))
      isUnitOfElement,
     do
      let x := (← getMainTarget).consumeMData.appArg!
      if x.isAppOfArity ``HMul.hMul 6 then
        evalTactic (← `(tactic| refine @invertibleMul _ _ _ _ ?_ ?_))
      else if x.isAppOfArity ``HPow.hPow 6 then
        evalTactic (← `(tactic| refine @invertiblePow _ _ _ ?_ _))
      else if x.isAppOfArity ``Neg.neg 3 then
        evalTactic (← `(tactic| refine @invertibleNeg _ _ _ _ _ ?_))
      else
        throwError "not a product, power or negative of units"
      for goal in ← getGoals do
        setGoals [goal]
        invertibleCases]

end CasCatalogue.Algebra.Units

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.units"⟩, category := CategoryId.sets, name := "Units"
    declaration := `CasCatalogue.Algebra.Units.units
    inclusion := some `CasCatalogue.Algebra.Units.inclusion
    admission := some `CasCatalogue.Algebra.Units.admit
    evidence := some `CasCatalogue.Algebra.Units.invertibleEvidence }

normalized_registry .morphism
  { id := ⟨"mor.sets.units_inverse"⟩, category := CategoryId.sets, name := "⁻¹"
    declaration := `CasCatalogue.Algebra.Units.inverse }

normalized_registry .morphism
  { id := ⟨"mor.sets.divide"⟩, category := CategoryId.sets, name := "/"
    declaration := `CasCatalogue.Algebra.Units.divide }

end CasCatalogue
