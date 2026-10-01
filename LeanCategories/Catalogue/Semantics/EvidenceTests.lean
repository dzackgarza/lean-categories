/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units
public meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public meta import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public meta import Lean.Meta.Closure

@[expose] public section

/-!
# Tests of the registered membership evidence (LC-18)

Each domain's registered evidence is run, as a consumer runs it, through `Lean.Elab.Tactic.run`
on the admission's hypothesis at closed values. A value of the domain is established, and the
proof is checked by the kernel; a value outside the domain is refused (the procedure fails).
-/

namespace CasCatalogue.EvidenceTests

open Lean Meta Elab Tactic

/-- The row `row` registers `procedure` as its evidence. -/
meta def expectRegistered (row : String) (procedure : Name) : MetaM Unit := do
  let state ← semanticState
  let some entry := state.objects.find? (·.id.raw == row)
    | throwError "{row} is not registered"
  unless entry.evidence == some procedure do
    throwError "{row} registers the evidence {entry.evidence}, not {procedure}"

/-- Run `procedure` on the closed statement `statement` through `Lean.Elab.Tactic.run`. `some`
proof when it closes the goal with a `sorry`-free proof that the kernel accepts; `none` when it
fails. A procedure that returns with goals open is an error of the procedure. -/
meta def run (procedure : TacticM Unit) (statement : Term) : TermElabM (Option Expr) := do
  let type ← Term.elabType statement
  Term.synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  if type.hasMVar then throwError "the statement{indentExpr type}\nis not closed"
  let goal ← mkFreshExprMVar type
  let saved ← saveState
  let remaining ← try Tactic.run goal.mvarId! procedure catch _ => saved.restore; return none
  unless remaining.isEmpty do
    throwError "the evidence returned with {remaining.length} goal(s) open on{indentExpr type}"
  let proof ← instantiateMVars goal
  if proof.hasSorry || proof.hasMVar then
    throwError "the evidence proved{indentExpr type}\nwith `sorry` or a metavariable"
  -- The kernel checks the proof, or the data (the inverse of a unit, `Invertible x`).
  if ← isProp type then
    discard <| mkAuxTheorem type proof
  else
    discard <| mkAuxDefinition (← mkFreshUserName `evidence) type proof (compile := false)
  return some proof

/-- The hypothesis of `Monicₙ(K)` at `p` and `n`: `p.Monic ∧ p.natDegree = n`. -/
meta def monicOfDegree (p n : Term) : TermElabM Term :=
  `(Polynomial.Monic $p ∧ Polynomial.natDegree $p = $n)

/-- `procedure` establishes each statement. -/
meta def expectEstablished (procedure : TacticM Unit) (statements : List Term) :
    TermElabM Unit := do
  for statement in statements do
    if (← run procedure statement).isNone then
      throwError "the evidence does not establish {statement}"

/-- `procedure` refuses each statement: it fails, establishing nothing. -/
meta def expectRefused (procedure : TacticM Unit) (statements : List Term) :
    TermElabM Unit := do
  for statement in statements do
    if (← run procedure statement).isSome then
      throwError "the evidence establishes {statement}, which is false"

end CasCatalogue.EvidenceTests

namespace CasCatalogue.EvidenceTests

open CasCatalogue.Algebra

/-! ## `Mˣ ↪ M`: `Invertible x`, the inverse of `x`

The registered evidence establishes `Invertible x`; `isUnitEvidence`, which it runs on the
equations of the inverse, establishes `IsUnit x` on the same elements. -/

/-- The elements of closed monoids that are units. -/
meta def unitSpecimens : Lean.Elab.Term.TermElabM (List Lean.Term) := do
  return [← `((2 : ℚ)), ← `((-3 / 4 : ℝ)),
      ← `((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ)),
      ← `((5 : ZMod 7)), ← `((-1 : ℤ)),
      ← `((!![1, 2, 0; 3, 4, 1; 0, 5, 7] : Matrix (Fin 3) (Fin 3) ℚ)),
      ← `((!![2, 1, 0, 0; 0, 1, 3, 0; 1, 0, 1, 1; 0, 2, 0, 5] : Matrix (Fin 4) (Fin 4) ℚ)),
      ← `((!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ)),
      ← `((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2))),
      ← `((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)),
      ← `((1 : ℕ)), ← `((3 : ZMod 10)), ← `((-(7 : ZMod 12))),
      ← `(((-1 : ℤ) ^ 5)), ← `((Real.pi)), ← `((Real.sqrt 2)),
      ← `((2 + 3 * Complex.I)), ← `((Complex.I)),
      ← `((1 / 3 - 1 / 4 : ℚ)), ← `(((2 : ZMod 9) * 4 ^ 3)),
      ← `((Equiv.swap (0 : Fin 3) 1 : Equiv.Perm (Fin 3)))]

/-- The elements of closed monoids that are not units. -/
meta def nonunitSpecimens : Lean.Elab.Term.TermElabM (List Lean.Term) := do
  return [← `((2 : ℤ)), ← `((0 : ℚ)),
      ← `((!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ)),
      ← `((!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)),
      ← `((!![1, 2, 3; 4, 5, 6; 7, 8, 9] : Matrix (Fin 3) (Fin 3) ℚ)),
      ← `((2 : ℕ)), ← `((0 : ℕ)), ← `((2 : ZMod 4)),
      ← `((6 : ZMod 9)), ← `(((2 : ℤ) * 3)), ← `((1 / 2 - 2 / 4 : ℚ))]

#guard_msgs in
run_meta expectRegistered "obj.sets.units" ``Units.invertibleEvidence

#guard_msgs in
run_elab do
  let units ← unitSpecimens
  expectEstablished Units.invertibleEvidence (← units.mapM fun x => `(Invertible $x))
  expectEstablished Units.isUnitEvidence (← units.mapM fun x => `(IsUnit $x))

#guard_msgs in
run_elab do
  let nonunits ← nonunitSpecimens
  expectRefused Units.invertibleEvidence (← nonunits.mapM fun x => `(Invertible $x))
  expectRefused Units.isUnitEvidence (← nonunits.mapM fun x => `(IsUnit $x))

/-! ### The registered numerals of `ℤ/n`

A consumer forms the numeral `k ∈ ℤ/n` (`obj.sets.integers_mod`, `n ≠ 0`) with the registered
numeral `num.sets.fin`: `ℤ/n` is `Fin n` by definition (Mathlib `ZMod`), so `finPoint` at
`1 ⟶ ℤ/n` unifies `n` as `m + 1` and the element is the point `⟨k, _⟩ : Fin (m + 1)`, a value of
`ℤ/n` carrying the ring structure of `ZMod n`. The evidence runs on that term. -/

section ZModNumerals

open Lean Meta Elab Term

/-- The value in `ℤ/n` of the registered numeral `k` at `1 ⟶ ℤ/n`, evaluated at the point of `1`
as a consumer evaluates it: the term `⟨k, _⟩ : Fin (m + 1)`. -/
meta def zmodNumeralValue (n k : Nat) : TermElabM Term := do
  let numeral ← `((CasCatalogue.Foundation.Morphisms.finPoint _ $(quote k) (by decide) :
      Foundation.Objects.fin 1 ⟶ Foundation.Objects.integersMod $(quote n)))
  let element ← Term.elabTerm (← `(CategoryTheory.ConcreteCategory.hom (C := Type) $numeral
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← whnf (← instantiateMVars element)
  unless value.isAppOfArity ``Fin.mk 3 do
    throwError "the numeral {k} of ℤ/{n} evaluates to{indentExpr value}\nnot a point of Fin"
  Term.exprToSyntax value

/-- `Invertible x ∈ ℤ/n` at the registered numeral `x = k`, the statement formed at type `ℤ/n`
with the ring structure of `ZMod n`. -/
meta def zmodNumeralInvertible (n k : Nat) : TermElabM Term := do
  `(@Invertible (Foundation.Objects.integersMod $(quote n)) _ _ $(← zmodNumeralValue n k))

/-- `IsUnit x ∈ ℤ/n` at the registered numeral `x = k`. -/
meta def zmodNumeralIsUnit (n k : Nat) : TermElabM Term := do
  `(@IsUnit (Foundation.Objects.integersMod $(quote n)) _ $(← zmodNumeralValue n k))

/-- The registered numerals that are units: `2 ∈ ℤ/5`, `7 ∈ ℤ/12`, `3 ∈ ℤ/10`, `8 ∈ ℤ/9`,
`1 ∈ ℤ/2`. -/
meta def zmodNumeralUnits : List (Nat × Nat) := [(5, 2), (12, 7), (10, 3), (9, 8), (2, 1)]

/-- The registered numerals that are not: `5 ∈ ℤ/10`, `8 ∈ ℤ/12`, `0 ∈ ℤ/5`, `6 ∈ ℤ/9`. -/
meta def zmodNumeralNonunits : List (Nat × Nat) := [(10, 5), (12, 8), (5, 0), (9, 6)]

#guard_msgs in
run_elab do
  expectEstablished Units.invertibleEvidence
    (← zmodNumeralUnits.mapM fun (n, k) => zmodNumeralInvertible n k)
  expectEstablished Units.isUnitEvidence
    (← zmodNumeralUnits.mapM fun (n, k) => zmodNumeralIsUnit n k)

#guard_msgs in
run_elab do
  expectRefused Units.invertibleEvidence
    (← zmodNumeralNonunits.mapM fun (n, k) => zmodNumeralInvertible n k)
  expectRefused Units.isUnitEvidence
    (← zmodNumeralNonunits.mapM fun (n, k) => zmodNumeralIsUnit n k)

end ZModNumerals

/-! ## `R[x] ∖ {0} ↪ R[x]`: `p ≠ 0` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.nonzero_polynomials" ``Polynomials.nonzeroPolynomialEvidence

#guard_msgs in
run_elab do
  expectEstablished Polynomials.nonzeroPolynomialEvidence
    [← `((Polynomial.X ^ 2 + 1 : Polynomial ℚ) ≠ 0),
      ← `((Polynomial.C (3 / 4) : Polynomial ℚ) ≠ 0),
      ← `(((Polynomial.X + 1) ^ 2 - Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ) ≠ 0),
      ← `((Polynomial.X ^ 3 - 2 : Polynomial ℤ) ≠ 0),
      ← `(((Polynomial.X - 1) * (Polynomial.X + 1) : Polynomial ℤ) ≠ 0),
      ← `((2 * Polynomial.X : Polynomial ℤ) ≠ 0),
      ← `((Polynomial.X ^ 5 - Polynomial.X ^ 5 + 3 : Polynomial ℤ) ≠ 0),
      ← `((Polynomial.C Real.pi * Polynomial.X ^ 3 + 1 : Polynomial ℝ) ≠ 0),
      ← `((Polynomial.C (Real.sqrt 2) : Polynomial ℝ) ≠ 0),
      ← `((Polynomial.X ^ 2 + Polynomial.C Complex.I : Polynomial ℂ) ≠ 0),
      ← `((Polynomial.C (2 + Complex.I) * Polynomial.X : Polynomial ℂ) ≠ 0),
      ← `((Polynomial.X ^ 100 - Polynomial.X : Polynomial ℚ) ≠ 0)]

#guard_msgs in
run_elab do
  expectRefused Polynomials.nonzeroPolynomialEvidence
    [← `((0 : Polynomial ℚ) ≠ 0),
      ← `((Polynomial.X - Polynomial.X : Polynomial ℚ) ≠ 0),
      ← `(((Polynomial.X + 1) ^ 2 - Polynomial.X ^ 2 - 2 * Polynomial.X - 1 : Polynomial ℤ) ≠ 0),
      ← `((Polynomial.C 0 : Polynomial ℝ) ≠ 0),
      ← `((2 * Polynomial.X - Polynomial.X - Polynomial.X : Polynomial ℂ) ≠ 0)]

/-! ## `Monicₙ(K) ↪ K[x]`: `p.Monic ∧ p.natDegree = n` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.monics" ``LinearAlgebra.monicEvidence

#guard_msgs in
run_elab do
  expectEstablished LinearAlgebra.monicEvidence
    [← monicOfDegree (← `((Polynomial.X ^ 3 + 2 * Polynomial.X + 1 : Polynomial ℚ))) (← `(3)),
      ← monicOfDegree (← `(((Polynomial.X + 1) ^ 2 * (Polynomial.X - 3) : Polynomial ℤ)))
        (← `(3)),
      ← monicOfDegree
        (← `((Polynomial.X ^ 2 - Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℚ))) (← `(1)),
      ← monicOfDegree (← `((Polynomial.X : Polynomial (ZMod 5)))) (← `(1)),
      ← monicOfDegree (← `((7 * Polynomial.X ^ 3 + Polynomial.X ^ 2 : Polynomial (ZMod 7))))
        (← `(2)),
      ← monicOfDegree (← `((Polynomial.X ^ 4 - Polynomial.C (1 / 2) : Polynomial ℚ))) (← `(4)),
      ← monicOfDegree (← `((1 : Polynomial ℤ))) (← `(0)),
      ← monicOfDegree
        (← `((Polynomial.X ^ 2 + Polynomial.C Real.pi * Polynomial.X : Polynomial ℝ))) (← `(2)),
      ← monicOfDegree (← `((Polynomial.X ^ 2 + Polynomial.C Complex.I : Polynomial ℂ)))
        (← `(2)),
      -- `8 = 1` in `ℤ/7`.
      ← monicOfDegree (← `((8 * Polynomial.X ^ 2 + Polynomial.X : Polynomial (ZMod 7))))
        (← `(2))]

#guard_msgs in
run_elab do
  expectRefused LinearAlgebra.monicEvidence
    [← monicOfDegree (← `((Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 : Polynomial ℚ))) (← `(3)),
      ← monicOfDegree (← `((Polynomial.X ^ 3 + 1 : Polynomial ℚ))) (← `(2)),
      ← monicOfDegree (← `((2 * Polynomial.X ^ 2 + 1 : Polynomial ℤ))) (← `(2)),
      ← monicOfDegree (← `((0 : Polynomial ℚ))) (← `(0)),
      ← monicOfDegree (← `((Polynomial.X ^ 2 - Polynomial.X ^ 2 : Polynomial ℚ))) (← `(2)),
      ← monicOfDegree (← `((6 * Polynomial.X ^ 2 + Polynomial.X : Polynomial (ZMod 7))))
        (← `(2)),
      ← monicOfDegree (← `((7 * Polynomial.X ^ 2 + Polynomial.X : Polynomial (ZMod 7))))
        (← `(2))]

/-! ## `C(ℝ) ↪ (ℝ → ℝ)`: `Continuous f` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.continuous_maps" ``Calculus.continuousEvidence

#guard_msgs in
run_elab do
  expectEstablished Calculus.continuousEvidence
    [← `(Continuous (fun x : ℝ => x)), ← `(Continuous (fun _ : ℝ => (3 : ℝ))),
      ← `(Continuous (fun x : ℝ => x ^ 3 - 2 * x + 1)),
      ← `(Continuous (fun x : ℝ => Real.sin x * Real.cos x)),
      ← `(Continuous (fun x : ℝ => Real.exp (Real.sin (x ^ 2 + 3)) - Real.pi * x)),
      ← `(Continuous (fun x : ℝ => Real.cos (Real.exp x) ^ 2 + Real.sin x ^ 2)),
      ← `(Continuous (Real.sin ∘ Real.exp)), ← `(Continuous Real.cos),
      ← `(Continuous (fun x : ℝ => Real.sin x / (x ^ 2 + 1))),
      ← `(Continuous (fun x : ℝ => x / Real.exp x))]

#guard_msgs in
run_elab do
  expectRefused Calculus.continuousEvidence
    [← `(Continuous (fun x : ℝ => if x < 0 then (0 : ℝ) else 1)),
      ← `(Continuous (fun x : ℝ => 1 / x)),
      ← `(Continuous (fun x : ℝ => Real.sin x / Real.sin x)),
      ← `(Continuous (fun x : ℝ => (Int.floor x : ℝ)))]

/-! ## `C^∞(ℝ) ↪ (ℝ → ℝ)`: `ContDiff ℝ ∞ f` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.smooth_maps" ``Calculus.smoothEvidence

#guard_msgs in
run_elab do
  expectEstablished Calculus.smoothEvidence
    [← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x)),
      ← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x ^ 5 - 3 * x ^ 2 + 7)),
      ← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => Real.sin x * Real.exp x)),
      ← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => Real.exp (Real.cos (x ^ 2)) + Real.pi)),
      ← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.cos ∘ Real.sin)),
      ← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => Real.exp x / (x ^ 2 + 1)))]

#guard_msgs in
run_elab do
  expectRefused Calculus.smoothEvidence
    [← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => |x|)),
      ← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => Real.sqrt x)),
      ← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => if x < 0 then (0 : ℝ) else x ^ 2)),
      ← `(ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => 1 / x))]

/-! ## `ℕ⁺ ↪ ℕ`: `0 < n` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.positive_naturals" ``Semirings.positiveEvidence

#guard_msgs in
run_elab do
  expectEstablished Semirings.positiveEvidence
    [← `(0 < 1), ← `(0 < 2), ← `(0 < 2 ^ 100 - 3), ← `(0 < 7 * 13 + 1),
      ← `(0 < Nat.factorial 5), ← `(0 < 1000000007 % 97), ← `(0 < 10 / 3)]

#guard_msgs in
run_elab do
  expectRefused Semirings.positiveEvidence
    [← `(0 < 0), ← `(0 < 3 - 5), ← `(0 < 2 * 0 + 0), ← `(0 < 2 / 3), ← `(0 < 91 % 7)]

/-! ## `ℙ ↪ ℕ`: `n.Prime` -/

#guard_msgs in
run_meta expectRegistered "obj.sets.primes" ``Semirings.primeEvidence

#guard_msgs in
run_elab do
  expectEstablished Semirings.primeEvidence
    [← `(Nat.Prime 2), ← `(Nat.Prime 3), ← `(Nat.Prime 97), ← `(Nat.Prime 1000003),
      ← `(Nat.Prime (2 ^ 19 - 1)), ← `(Nat.Prime (2 ^ 5 - 1)), ← `(Nat.Prime (Nat.factorial 3 + 1)),
      ← `(Nat.Prime (10 ^ 6 + 3))]

#guard_msgs in
run_elab do
  expectRefused Semirings.primeEvidence
    [← `(Nat.Prime 0), ← `(Nat.Prime 1), ← `(Nat.Prime 91), ← `(Nat.Prime (2 ^ 11 - 1)),
      ← `(Nat.Prime 1000001), ← `(Nat.Prime 561)]

end CasCatalogue.EvidenceTests
