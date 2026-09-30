/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic
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
* An element `x ∈ M` is a unit only with the evidence `IsUnit x` (the admission); without it, it
  is not an element of `Mˣ`, and `x⁻¹` is not a term.
* `⁻¹ : Mˣ → Mˣ`, and division `M × Mˣ → M`, `(a, u) ↦ a u⁻¹`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.Units

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- `Mˣ`. -/
abbrev units (M : Type) [Monoid M] : SetsCat.{0} := Mˣ

/-- `Mˣ ↪ M`. -/
def inclusion (M : Type) [Monoid M] : units M ⟶ (M : SetsCat.{0}) := TypeCat.ofHom Units.val

/-- The unit `x`, with the evidence that `x` is a unit. -/
noncomputable def admit (M : Type) [Monoid M] (x : M) (h : IsUnit x) : fin 1 ⟶ units M :=
  TypeCat.ofHom fun _ => h.unit

/-- In `ℤ/n` with `n ≠ 0`, `x` is a unit exactly when its representative `x.val ∈ [0, n)` is
coprime to `n` (Mathlib `ZMod.isUnit_iff_coprime`, stated there for the image of a natural
number). -/
theorem zmod_isUnit_iff_coprime_val {n : ℕ} [NeZero n] (x : ZMod n) :
    IsUnit x ↔ x.val.Coprime n := by
  rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]

open Lean Elab Tactic in
/-- The evidence that a closed element `x` of a division ring is nonzero: `x` is evaluated
(numerals, field operations, `re`/`im` of complex numbers), and a positive real expression (`π`,
`√a`, `exp a`) is nonzero because it is positive. -/
meta def nonzeroEvidence : TacticM Unit :=
  CasCatalogue.Evidence.closeByFirst m!"the value is not established to be nonzero"
    [do evalTactic (← `(tactic| norm_num)),
     do evalTactic (← `(tactic| positivity)),
     do evalTactic (← `(tactic| norm_num [Complex.ext_iff])),
     do evalTactic (← `(tactic| decide))]

open Lean Elab Tactic in
/-- The units of the monoids of closed values, by the structure of the monoid `M`:

* every element of a group is a unit (`Mˣ`, `GLₙ(K)`, permutations);
* a square matrix over a commutative ring is a unit iff its determinant is
  (`Matrix.isUnit_iff_isUnit_det`); the determinant of a matrix of closed entries is expanded
  along its first row (`Matrix.det_succ_row_zero`) and its units are those of the ring;
* in a division ring (`ℚ`, `ℝ`, `ℂ`) the units are the nonzero elements (`isUnit_iff_ne_zero`);
* the units of `ℤ` are `±1` (`Int.isUnit_iff`), of `ℕ` only `1` (`Nat.isUnit_iff`);
* the units of `ℤ/n`, `n ≠ 0`, are the classes coprime to `n` (`zmod_isUnit_iff_coprime_val`);
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
      evalTactic (← `(tactic| try simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
        Matrix.submatrix_apply, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
        Fin.zero_succAbove, Fin.succAbove_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.det_unique, Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton,
        Fin.val_zero, Fin.val_succ, Matrix.of_apply, Matrix.cons_val_fin_one, Matrix.head_cons,
        Matrix.det_isEmpty, Matrix.det_one, Matrix.det_mul, Matrix.det_transpose,
        Matrix.det_diagonal, Fin.prod_univ_succ, Fin.prod_univ_zero]))
      isUnitCases,
     do
      evalTactic (← `(tactic| rw [isUnit_iff_ne_zero]))
      nonzeroEvidence,
     do
      evalTactic (← `(tactic| rw [Int.isUnit_iff]))
      CasCatalogue.Evidence.closeByFirst m!"not ±1"
        [do evalTactic (← `(tactic| norm_num)), do evalTactic (← `(tactic| decide))],
     do
      evalTactic (← `(tactic| rw [Nat.isUnit_iff]))
      CasCatalogue.Evidence.closeByFirst m!"not 1"
        [do evalTactic (← `(tactic| norm_num)), do evalTactic (← `(tactic| decide))],
     do
      evalTactic (← `(tactic|
        rw [CasCatalogue.Algebra.Units.zmod_isUnit_iff_coprime_val]))
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

/-- `u ↦ u⁻¹`, the inverse of the group `Mˣ`. -/
def inverse (M : Type) [Monoid M] : units M ⟶ units M := TypeCat.ofHom fun u => u⁻¹

/-- `(a, u) ↦ a u⁻¹`. -/
def divide (M : Type) [Monoid M] : (M × units M : SetsCat.{0}) ⟶ (M : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 * ↑(p.2⁻¹)

end CasCatalogue.Algebra.Units

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.units"⟩, category := CategoryId.sets, name := "Units"
    declaration := `CasCatalogue.Algebra.Units.units
    inclusion := some `CasCatalogue.Algebra.Units.inclusion
    admission := some `CasCatalogue.Algebra.Units.admit
    evidence := some `CasCatalogue.Algebra.Units.isUnitEvidence }

normalized_registry .morphism
  { id := ⟨"mor.sets.units_inverse"⟩, category := CategoryId.sets, name := "⁻¹"
    declaration := `CasCatalogue.Algebra.Units.inverse }

normalized_registry .morphism
  { id := ⟨"mor.sets.divide"⟩, category := CategoryId.sets, name := "/"
    declaration := `CasCatalogue.Algebra.Units.divide }

end CasCatalogue
