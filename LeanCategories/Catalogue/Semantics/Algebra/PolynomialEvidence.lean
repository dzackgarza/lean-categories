/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Data.Int.CharZero
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Ring
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Evidence for nonzero polynomial expressions

The existing polynomial-domain evidence is kept at its reusable proof owner, independently
of the objects that use it. Both nonzero polynomials and finite polynomial-root subsets
require exactly this same nonvanishing obligation. Declaration names and proof procedures
are preserved from `Algebra/Polynomials.lean`.
-/

namespace CasCatalogue.Algebra.Polynomials

open CategoryTheory Polynomial
open Lean Elab Tactic

open Lean Elab Tactic in
/-- Close each remaining goal, a closed arithmetic fact about coefficients or degrees
(`Units.closedArithmeticEvidence`). -/
meta def closeCoefficientGoals : TacticM Unit := do
  for goal in ← getUnsolvedGoals do
    setGoals [goal]
    CasCatalogue.Algebra.Units.closedArithmeticEvidence

open Lean Elab Tactic in
/-- Put a closed polynomial expression in normal form: the catalogue's numerals evaluated
(`Units.evaluateNumerals`), coefficients reduced modulo the characteristic of `ℤ/n`, a constant
that reduces to `0` or `1` read as that element of `R[x]` (`C 0 = 0`, `C 1 = 1`), and the
expression expanded into a sum of monomials `c·xᵏ` with like terms collected (commutative-ring
normalization), so that cancelling and vanishing leading terms disappear. -/
meta def normalizePolynomial : TacticM Unit := do
  CasCatalogue.Algebra.Units.evaluateNumerals
  evalTactic (← `(tactic| try reduce_mod_char))
  evalTactic (← `(tactic| try simp only [map_zero, map_one]))
  evalTactic (← `(tactic| try ring_nf))

open Lean Elab Tactic in
/-- `p ≠ 0` because `deg p = d` for a natural number `d` (`Polynomial.ne_zero_of_coe_le_degree`):
the degree of the closed expression is computed from its terms (Mathlib `compute_degree`), which
leaves the leading coefficient `≠ 0` as a closed arithmetic fact. -/
meta def nonzeroByDegree : TacticM Unit := do
  evalTactic (← `(tactic|
    refine Polynomial.ne_zero_of_coe_le_degree (n := ?_) (le_of_eq (Eq.symm ?_))))
  -- The degree `d` is the one `compute_degree` reads off `deg p = d`.
  let goals ← getGoals
  let some degreeGoal ← goals.findM? fun goal => return (← goal.getType).isAppOf ``Eq
    | throwError "no degree equation `deg p = d`"
  setGoals [degreeGoal]
  evalTactic (← `(tactic| compute_degree!))
  closeCoefficientGoals
  setGoals (← goals.filterM fun goal => return !(← goal.isAssigned))

/-- A ring map `f : R → S` out of a simple ring `R` (every division ring: `ℚ`, `ℝ`, `ℂ`) into a
ring with `0 ≠ 1` is injective: its kernel is a two-sided ideal of `R` not containing `1`, hence
`0` (Mathlib `RingHom.injective`). -/
theorem injective_of_isSimpleRing {R S : Type*} [NonAssocRing R] [IsSimpleRing R]
    [NonAssocSemiring S] (f : R →+* S) (h : (0 : S) ≠ 1) : Function.Injective f :=
  haveI := nontrivial_of_ne _ _ h
  f.injective

open Lean Elab Tactic in
/-- The evidence that a ring map `f : R → S` between closed rings is injective, by the structure
of `f` and of its domain:

* a map out of a simple ring (a division ring: `ℚ`, `ℝ`, `ℂ`) into a ring in which `0 ≠ 1`
  (`injective_of_isSimpleRing`; `0 ≠ 1` in `S` is a closed arithmetic fact);
* a map out of `ℤ` into a ring of characteristic zero: it is `n ↦ n · 1`, injective exactly in
  characteristic zero (Mathlib `RingHom.injective_int`);
* the structure map `R → A` of a faithful `R`-algebra (Mathlib `FaithfulSMul.algebraMap_injective`);
* the identity, and a composite of injective maps (`RingHom.coe_comp`, `Function.Injective.comp`).

It fails on a map not established to be injective (`ℤ → ℤ/n`). -/
meta partial def injectiveRingHomEvidence : TacticM Unit :=
  CasCatalogue.Evidence.closeByFirst m!"the ring map is not established to be injective"
    [do
      evalTactic (← `(tactic|
        refine CasCatalogue.Algebra.Polynomials.injective_of_isSimpleRing _ ?_))
      closeCoefficientGoals,
     do evalTactic (← `(tactic| exact RingHom.injective_int _)),
     do evalTactic (← `(tactic| exact FaithfulSMul.algebraMap_injective _ _)),
     do
      evalTactic (← `(tactic| rw [RingHom.coe_id]))
      evalTactic (← `(tactic| exact Function.injective_id)),
     do
      evalTactic (← `(tactic| rw [RingHom.coe_comp]))
      evalTactic (← `(tactic| refine Function.Injective.comp ?_ ?_))
      for goal in ← getGoals do
        setGoals [goal]
        injectiveRingHomEvidence]

open Lean Elab Tactic in
/-- The evidence that a closed polynomial `p ∈ R[x]` is nonzero, by the structure of `p`:

* `p` an expression in `x`, constants `C r`, numerals, `+`, `-`, `·`, `^` over a closed
  commutative ring `R` (`ℤ`, `ℚ`, `ℝ`, `ℂ`, `ℤ/n`): a polynomial is nonzero exactly when it has a
  degree `d ∈ ℕ`, i.e. a nonzero leading coefficient. The degree is read off the expression, and,
  when its naive leading terms cancel, off its normal form;
* `p = q.map f` the image of `q ∈ R[x]` along an injective ring map `f : R → S`: it is nonzero
  exactly when `q` is (Mathlib `Polynomial.map_ne_zero_iff`), so `q ≠ 0` is established by this
  procedure and the injectivity of `f` by `injectiveRingHomEvidence`.

It fails on the zero polynomial. -/
meta partial def nonzeroPolynomialEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "R[x] ∖ {0}" nonzeroCases
where
  /-- The cases above, tried in turn on the main goal `p ≠ 0`. -/
  nonzeroCases : TacticM Unit :=
    CasCatalogue.Evidence.closeByFirst m!"the polynomial is not established to be nonzero"
      [nonzeroOfMap, nonzeroByDegree, do normalizePolynomial; nonzeroByDegree]
  /-- `q.map f ≠ 0` from `q ≠ 0` and the injectivity of `f`. -/
  nonzeroOfMap : TacticM Unit := do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``Ne 3 && (target.getArg! 1).isAppOfArity ``Polynomial.map 6 do
      throwError "not the image of a polynomial along a ring map"
    evalTactic (← `(tactic| refine (Polynomial.map_ne_zero_iff ?_).mpr ?_))
    for goal in ← getGoals do
      setGoals [goal]
      if (← instantiateMVars (← goal.getType)).consumeMData.isAppOf ``Function.Injective then
        injectiveRingHomEvidence
      else
        nonzeroCases

end CasCatalogue.Algebra.Polynomials
