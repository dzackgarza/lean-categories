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
public import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
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

/-! ### The numerals of `ℤ/n`

The numeral `k` of `ℤ/n` is the image of `k` under the initial ring map `ℤ → ℤ/n`
(`num.rings` at `obj.rings.integers_mod`, LC-15), an element of the set underlying the ring
`ℤ/n`. A position `k` of `Fin n` is an element of `ℤ/n` only through the registered map
`Fin n ↪ ℤ/n` (`incl.sets.fin_integers_mod`), which carries it to that numeral
(`NumberSystems.finPoint_finIntegersMod`). The evidence runs on both terms, as a consumer forms
them. -/

section ZModNumerals

open Lean Meta Elab Term

/-- The numeral `k` of the ring `ℤ/n`, evaluated at the point of `1`. -/
meta def zmodNumeralValue (n k : Nat) : TermElabM Term :=
  `(CategoryTheory.ConcreteCategory.hom (C := Type)
      (NamedRings.ringNumeral (NamedRings.ringIntegersMod $(quote n)) $(quote k))
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1))

/-- The position `k` of `Fin n` carried into `ℤ/n` by `Fin n ↪ ℤ/n`, at the point of `1`. -/
meta def zmodPositionValue (n k : Nat) : TermElabM Term :=
  `(CategoryTheory.ConcreteCategory.hom (C := Type)
      (CategoryTheory.CategoryStruct.comp
        (Foundation.Morphisms.finPoint $(quote n) $(quote k) (by decide))
        (NumberSystems.finIntegersMod $(quote n)))
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1))

/-- The numerals `k ∈ ℤ/n` that are units: `2 ∈ ℤ/5`, `7 ∈ ℤ/12`, `3 ∈ ℤ/10`, `8 ∈ ℤ/9`,
`1 ∈ ℤ/2`, `12 = 5 ∈ ℤ/7`. -/
meta def zmodNumeralUnits : List (Nat × Nat) :=
  [(5, 2), (12, 7), (10, 3), (9, 8), (2, 1), (7, 12)]

/-- The numerals that are not: `5 ∈ ℤ/10`, `8 ∈ ℤ/12`, `0 ∈ ℤ/5`, `6 ∈ ℤ/9`, `10 = 0 ∈ ℤ/5`. -/
meta def zmodNumeralNonunits : List (Nat × Nat) := [(10, 5), (12, 8), (5, 0), (9, 6), (5, 10)]

#guard_msgs in
run_elab do
  for (n, k) in zmodNumeralUnits do
    expectEstablished Units.invertibleEvidence [← `(Invertible $(← zmodNumeralValue n k))]
    expectEstablished Units.isUnitEvidence [← `(IsUnit $(← zmodNumeralValue n k))]
    if k < n then
      expectEstablished Units.invertibleEvidence [← `(Invertible $(← zmodPositionValue n k))]

#guard_msgs in
run_elab do
  for (n, k) in zmodNumeralNonunits do
    expectRefused Units.invertibleEvidence [← `(Invertible $(← zmodNumeralValue n k))]
    expectRefused Units.isUnitEvidence [← `(IsUnit $(← zmodNumeralValue n k))]
    if k < n then
      expectRefused Units.invertibleEvidence [← `(Invertible $(← zmodPositionValue n k))]

end ZModNumerals

/-! ### The numerals of a polynomial ring

The numeral `k` of the ring `R[x]` is the image of `k` under the initial ring map `ℤ → R[x]`
(LC-15), which is the constant `C k` of the numeral `k` of `R`, `C : R → R[x]` being a ring map.
A constant `C a` is a unit of `R[x]` exactly when `a` is a unit of `R` (Mathlib
`Polynomial.isUnit_C`): over a field `K`, the numeral `k` of `K[x]` is a unit iff `k ≠ 0` in `K`.
The evidence runs on the numeral as a consumer forms it. -/

section PolynomialNumerals

open Lean Meta Elab Term

/-- The numeral `k` of the ring `R[x]`, evaluated at the point of `1`. -/
meta def polynomialNumeralValue (R : Term) (k : Nat) : TermElabM Term :=
  `(CategoryTheory.ConcreteCategory.hom (C := Type)
      (NamedRings.ringNumeral (Polynomials.ringPolynomials $R) $(quote k))
      (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1))

/-- The numerals of `K[x]` that are units: `3, 1 ∈ ℚ[x]`, `2 ∈ ℝ[x]`, `2 ∈ 𝔽₅[x]`,
`7 = 2 ∈ 𝔽₅[x]`, `1 ∈ 𝔽₂[x]`. -/
meta def polynomialNumeralUnits : TermElabM (List (Term × Nat)) := do
  return [(← `(ℚ), 3), (← `(ℚ), 1), (← `(ℝ), 2), (← `(ZMod 5), 2), (← `(ZMod 5), 7),
    (← `(ZMod 2), 1)]

/-- The numerals that are not: `0 ∈ ℚ[x]`, `5 = 0`, `10 = 0 ∈ 𝔽₅[x]`, `2 = 0 ∈ 𝔽₂[x]`, and,
over a ring that is not a field, `2 ∈ ℤ[x]` (`2` is not a unit of `ℤ`). -/
meta def polynomialNumeralNonunits : TermElabM (List (Term × Nat)) := do
  return [(← `(ℚ), 0), (← `(ZMod 5), 5), (← `(ZMod 5), 10), (← `(ZMod 2), 2), (← `(ℤ), 2)]

#guard_msgs in
run_elab do
  for (R, k) in ← polynomialNumeralUnits do
    expectEstablished Units.invertibleEvidence [← `(Invertible $(← polynomialNumeralValue R k))]
    expectEstablished Units.isUnitEvidence [← `(IsUnit $(← polynomialNumeralValue R k))]

#guard_msgs in
run_elab do
  for (R, k) in ← polynomialNumeralNonunits do
    expectRefused Units.invertibleEvidence [← `(Invertible $(← polynomialNumeralValue R k))]
    expectRefused Units.isUnitEvidence [← `(IsUnit $(← polynomialNumeralValue R k))]
  -- Non-constant polynomials over a field are not units.
  expectRefused Units.invertibleEvidence
    [← `(Invertible (Polynomial.X : Polynomial ℚ)),
      ← `(Invertible (Polynomial.X + 1 : Polynomial (ZMod 5)))]

end PolynomialNumerals

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

/-! Images `q.map f` along injective ring maps: `q.map f ≠ 0` iff `q ≠ 0`. The injectivity of
`f` (out of a field, out of `ℤ` into characteristic zero, composites) is established by the
procedure. -/

#guard_msgs in
run_elab do
  expectEstablished Polynomials.nonzeroPolynomialEvidence
    [← `(((Polynomial.X ^ 3 - 2 * Polynomial.X + 1 : Polynomial ℚ).map (algebraMap ℚ ℂ)) ≠ 0),
      ← `(((Polynomial.X ^ 2 - 2 : Polynomial ℤ).map (Int.castRingHom ℚ)) ≠ 0),
      ← `(((Polynomial.X ^ 2 - 2 : Polynomial ℤ).map (algebraMap ℤ ℝ)) ≠ 0),
      ← `(((Polynomial.C Real.pi * Polynomial.X + 1 : Polynomial ℝ).map (algebraMap ℝ ℂ)) ≠ 0),
      ← `((((Polynomial.X + 1) ^ 2 - Polynomial.X ^ 2 - 2 * Polynomial.X : Polynomial ℚ).map
        (algebraMap ℚ ℝ)) ≠ 0),
      ← `((((Polynomial.X + 1 : Polynomial ℤ).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)) ≠ 0),
      ← `(((Polynomial.X ^ 2 + 1 : Polynomial ℤ).map
        ((algebraMap ℚ ℝ).comp (Int.castRingHom ℚ))) ≠ 0),
      ← `(((Polynomial.X : Polynomial (ZMod 5)).map (RingHom.id (ZMod 5))) ≠ 0)]

#guard_msgs in
run_elab do
  expectRefused Polynomials.nonzeroPolynomialEvidence
    [← `(((0 : Polynomial ℚ).map (algebraMap ℚ ℂ)) ≠ 0),
      ← `(((Polynomial.X - Polynomial.X : Polynomial ℤ).map (Int.castRingHom ℚ)) ≠ 0),
      ← `(((Polynomial.C 0 : Polynomial ℝ).map (algebraMap ℝ ℂ)) ≠ 0),
      -- `5 = 0` in `ℤ/5`: the image is `0`.
      ← `(((5 * Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod 5))) ≠ 0)]

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

/-! Images `q.map f` along ring maps into rings with `0 ≠ 1`: monic of degree `n` when `q` is,
whether or not `f` is injective. -/

#guard_msgs in
run_elab do
  expectEstablished LinearAlgebra.monicEvidence
    [← monicOfDegree
        (← `(((Polynomial.X ^ 2 + 2 * Polynomial.X + 1 : Polynomial ℚ).map (algebraMap ℚ ℝ))))
        (← `(2)),
      ← monicOfDegree (← `(((Polynomial.X ^ 3 - 2 : Polynomial ℤ).map (Int.castRingHom ℚ))))
        (← `(3)),
      ← monicOfDegree
        (← `(((Polynomial.X ^ 2 - Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ).map
          (algebraMap ℤ ℚ)))) (← `(1)),
      ← monicOfDegree
        (← `(((Polynomial.X ^ 2 + Polynomial.C Real.pi * Polynomial.X : Polynomial ℝ).map
          (algebraMap ℝ ℂ)))) (← `(2)),
      ← monicOfDegree
        (← `((((Polynomial.X ^ 4 - Polynomial.C (1 / 2) : Polynomial ℚ).map
          (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)))) (← `(4)),
      -- `ℤ → ℤ/5` is not injective; `x² + 5 ↦ x²` is monic of degree `2`.
      ← monicOfDegree
        (← `(((Polynomial.X ^ 2 + 5 : Polynomial ℤ).map (Int.castRingHom (ZMod 5))))) (← `(2))]

#guard_msgs in
run_elab do
  expectRefused LinearAlgebra.monicEvidence
    [← monicOfDegree (← `(((0 : Polynomial ℚ).map (algebraMap ℚ ℝ)))) (← `(0)),
      ← monicOfDegree (← `(((2 * Polynomial.X ^ 2 + 1 : Polynomial ℤ).map (Int.castRingHom ℚ))))
        (← `(2)),
      ← monicOfDegree (← `(((Polynomial.X ^ 3 + 1 : Polynomial ℚ).map (algebraMap ℚ ℝ))))
        (← `(2)),
      ← monicOfDegree
        (← `(((Polynomial.X ^ 2 - Polynomial.X ^ 2 : Polynomial ℚ).map (algebraMap ℚ ℂ))))
        (← `(2)),
      -- In the zero ring `ℤ/1` the image of `x` is `0`, of degree `0`.
      ← monicOfDegree (← `(((Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod 1)))))
        (← `(1))]

/-! ## Polynomials whose coefficients are the catalogue's numerals

The coefficient `k` of `R` is the numeral of the ring `R`, the image of `k` under `ℤ → R`
(`NamedRings.ringNumeral`, LC-15), as a consumer forms it; in `ℤ/n` it may vanish or reduce
(`4 = 0`, `6 = 2`, `5 = 1` in `ℤ/4`). -/

section NumeralCoefficients

open Lean Meta Elab Term

/-- The constant polynomial whose value is the numeral `k` of the ring `R`. -/
meta def numeralConstant (R : Term) (k : Nat) : TermElabM Term :=
  `(Polynomial.C (CategoryTheory.ConcreteCategory.hom (C := Type)
      (NamedRings.ringNumeral $R $(quote k)) (⟨0, Nat.one_pos⟩ : Foundation.Objects.fin 1)))

#guard_msgs in
run_elab do
  let Z ← `(NamedRings.ringIntegers)
  let Q ← `(NamedRings.ringRationals)
  let Z4 ← `(NamedRings.ringIntegersMod 4)
  expectEstablished Polynomials.nonzeroPolynomialEvidence
    [← `((Polynomial.X + $(← numeralConstant Z 3) : Polynomial ℤ) ≠ 0),
      ← `(($(← numeralConstant Z 3) * Polynomial.X ^ 2 + Polynomial.X : Polynomial ℤ) ≠ 0),
      ← `((Polynomial.X ^ 2 - $(← numeralConstant Q 2) : Polynomial ℚ) ≠ 0),
      ← `(($(← numeralConstant Z4 2) * Polynomial.X ^ 2 + Polynomial.X : Polynomial (ZMod 4)) ≠ 0),
      -- `4 = 0` in `ℤ/4`: the polynomial is `x`.
      ← `(($(← numeralConstant Z4 4) * Polynomial.X ^ 2 + Polynomial.X : Polynomial (ZMod 4)) ≠ 0),
      -- `6 = 2`, `5 = 1` in `ℤ/4`: `2x² + x`.
      ← `(($(← numeralConstant Z4 6) * Polynomial.X ^ 2 + $(← numeralConstant Z4 5) * Polynomial.X :
        Polynomial (ZMod 4)) ≠ 0)]
  expectRefused Polynomials.nonzeroPolynomialEvidence
    [← `(($(← numeralConstant Z4 4) : Polynomial (ZMod 4)) ≠ 0),
      ← `(($(← numeralConstant Z4 8) * Polynomial.X ^ 2 : Polynomial (ZMod 4)) ≠ 0),
      ← `(($(← numeralConstant Z 0) : Polynomial ℤ) ≠ 0),
      ← `(($(← numeralConstant Q 0) * Polynomial.X : Polynomial ℚ) ≠ 0)]

#guard_msgs in
run_elab do
  let Z ← `(NamedRings.ringIntegers)
  let Q ← `(NamedRings.ringRationals)
  let Z4 ← `(NamedRings.ringIntegersMod 4)
  expectEstablished LinearAlgebra.monicEvidence
    [← monicOfDegree (← `((Polynomial.X ^ 2 - $(← numeralConstant Q 2) : Polynomial ℚ))) (← `(2)),
      ← monicOfDegree
        (← `(($(← numeralConstant Z 1) * Polynomial.X ^ 2 + Polynomial.X : Polynomial ℤ))) (← `(2)),
      ← monicOfDegree (← `((Polynomial.X ^ 2 + $(← numeralConstant Z4 3) : Polynomial (ZMod 4))))
        (← `(2)),
      -- `4 = 0` in `ℤ/4`: `x`, monic of degree `1`.
      ← monicOfDegree (← `(($(← numeralConstant Z4 4) * Polynomial.X ^ 2 + Polynomial.X :
        Polynomial (ZMod 4)))) (← `(1)),
      -- `5 = 1` in `ℤ/4`: `x² + x`.
      ← monicOfDegree (← `(($(← numeralConstant Z4 5) * Polynomial.X ^ 2 + Polynomial.X :
        Polynomial (ZMod 4)))) (← `(2))]
  expectRefused LinearAlgebra.monicEvidence
    [← monicOfDegree
        (← `(($(← numeralConstant Z 2) * Polynomial.X ^ 2 + Polynomial.X : Polynomial ℤ))) (← `(2)),
      ← monicOfDegree (← `(($(← numeralConstant Z4 4) * Polynomial.X ^ 2 + Polynomial.X :
        Polynomial (ZMod 4)))) (← `(2)),
      ← monicOfDegree (← `(($(← numeralConstant Z4 3) * Polynomial.X ^ 2 + Polynomial.X :
        Polynomial (ZMod 4)))) (← `(2)),
      -- `6 = 2` in `ℤ/4`.
      ← monicOfDegree (← `(($(← numeralConstant Z4 6) * Polynomial.X ^ 2 + Polynomial.X :
        Polynomial (ZMod 4)))) (← `(2))]

end NumeralCoefficients

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
