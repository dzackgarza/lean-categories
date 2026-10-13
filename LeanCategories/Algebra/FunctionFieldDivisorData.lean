/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Function-field divisor data

Definition-level realization of Neukirch FC09-C01-U134.

The preceding source unit uses normalized discrete places of an algebraic
function field and the free abelian group on those places.  Here a normalized
place is represented by a surjective `ℤᵐ⁰`-valued valuation.  Its additive
order is the sign-reversed additive exponent of the multiplicative valuation,
so a uniformizer has order `+1`.

This file records the principal-divisor coefficient formula, selects its
finite-support realization and image subgroup, forms the quotient divisor
class group, records the residue-degree weighted degree of a divisor, selects
the descended degree function on classes, and defines the degree-zero class
subtype.  Finite support of principal divisors, closure of their image,
the product formula needed for quotient descent, homomorphism laws, and
finiteness of the degree-zero subgroup are result-layer statements.
-/

@[expose] public noncomputable section

open scoped WithZero

namespace LeanCategories.Algebra

universe u

/-- A normalized discrete place of a field, represented by a surjective
`ℤᵐ⁰`-valued valuation.  Surjectivity fixes the usual normalization rather
than retaining only the equivalence class of a rank-one discrete valuation. -/
structure NormalizedDiscretePlaceData (K : Type u) [Field K] where
  valuation : Valuation K ℤᵐ⁰
  normalized : Function.Surjective valuation

variable {K : Type u} [Field K]

/-- The additive order attached to a normalized discrete place.

Mathlib valuations are multiplicative and send a uniformizer to
`Multiplicative.ofAdd (-1)`; the minus sign converts this to Neukirch's
positive-on-uniformizers additive convention. -/
def normalizedPlaceOrderData
    (P : NormalizedDiscretePlaceData K) (f : Kˣ) : ℤ :=
  -((WithZero.unzero (P.valuation.ne_zero_iff.mpr (Units.ne_zero f))).toAdd)

/-- The divisor group on normalized places, i.e. the free abelian group
recorded in FC09-C01-U133. -/
abbrev FunctionFieldDivisorData (K : Type u) [Field K] :=
  NormalizedDiscretePlaceData K →₀ ℤ

/-- Coefficient characterization of the principal divisor
`div(f) = Σ_P ord_P(f) P`. -/
def IsFunctionFieldPrincipalDivisorData
    (f : Kˣ) (D : FunctionFieldDivisorData K) : Prop :=
  ∀ P : NormalizedDiscretePlaceData K, D P = normalizedPlaceOrderData P f

/-- The principal divisor of `f`, selected by its coefficient
characterization.  The finite-support theorem is deliberately deferred. -/
def functionFieldPrincipalDivisorData (f : Kˣ) : FunctionFieldDivisorData K :=
  Classical.epsilon (IsFunctionFieldPrincipalDivisorData f)

/-- The raw function `f ↦ div(f)`; its group-homomorphism law is result
content. -/
def functionFieldPrincipalDivisorMapData :
    Kˣ → FunctionFieldDivisorData K :=
  functionFieldPrincipalDivisorData

/-- Intrinsic carrier predicate for the image `P(K)` of principal
divisors. -/
def IsFunctionFieldPrincipalData (D : FunctionFieldDivisorData K) : Prop :=
  ∃ f : Kˣ, D = functionFieldPrincipalDivisorData f

/-- Predicate characterizing the subgroup `P(K)`. -/
def IsFunctionFieldPrincipalSubgroupData
    (P : AddSubgroup (FunctionFieldDivisorData K)) : Prop :=
  ∀ D : FunctionFieldDivisorData K, D ∈ P ↔ IsFunctionFieldPrincipalData D

/-- Neukirch's principal-divisor subgroup `P(K)`, selected by its intrinsic
carrier.  Closure is supplied later by the principal-divisor homomorphism. -/
def functionFieldPrincipalSubgroupData :
    AddSubgroup (FunctionFieldDivisorData K) :=
  Classical.epsilon (IsFunctionFieldPrincipalSubgroupData (K := K))

/-- The function-field divisor class group `Cl(K) = Div(K) / P(K)`. -/
abbrev FunctionFieldDivisorClassGroupData (K : Type u) [Field K] : Type u :=
  FunctionFieldDivisorData K ⧸ functionFieldPrincipalSubgroupData (K := K)

/-- Characterization of the residue degree of a place in characteristic `p`:
the finite residue field has cardinality `p ^ d`.

For the algebraic function fields in Neukirch's standing context, the later
finite-residue-field theorem identifies this `d` with
`[κ(P) : 𝔽_p]`. -/
def IsNormalizedPlaceDegreeData
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : NormalizedDiscretePlaceData K) (d : ℕ) : Prop :=
  Nat.card (IsLocalRing.ResidueField P.valuation.valuationSubring) = p ^ d

/-- The residue degree `[κ(P) : 𝔽_p]`, selected by its finite-field
cardinality characterization.

Existence of such a degree is the finite-residue-field result, not constructor
data. -/
def normalizedPlaceDegreeData
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : NormalizedDiscretePlaceData K) : ℤ :=
  (Classical.epsilon (IsNormalizedPlaceDegreeData (K := K) p P) : ℕ)

/-- Residue-degree weighted degree of a divisor
`Σ_P n_P [κ(P) : 𝔽_p]`. -/
def functionFieldDivisorDegreeData
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (D : FunctionFieldDivisorData K) : ℤ :=
  D.sum fun P n => n * normalizedPlaceDegreeData p P

/-- Predicate characterizing descent of divisor degree to the class-group
quotient.  The product formula is precisely the result which proves such a
function satisfies this predicate. -/
def IsFunctionFieldClassDegreeData
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (degree : FunctionFieldDivisorClassGroupData K → ℤ) : Prop :=
  ∀ D : FunctionFieldDivisorData K,
    degree (QuotientAddGroup.mk D) = functionFieldDivisorDegreeData p D

/-- The degree function on divisor classes, selected by its representative
formula.  Its well-definedness and additivity are result-layer consequences
of the product formula. -/
def functionFieldClassDegreeData
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    FunctionFieldDivisorClassGroupData K → ℤ :=
  Classical.epsilon (IsFunctionFieldClassDegreeData (K := K) p)

/-- Neukirch's degree-zero divisor classes `Cl⁰(K)`, before the later
finiteness theorem. -/
def FunctionFieldDegreeZeroClassData
    (p : ℕ) [Fact p.Prime] [CharP K p] : Type u :=
  {c : FunctionFieldDivisorClassGroupData K //
    functionFieldClassDegreeData (K := K) p c = 0}

end LeanCategories.Algebra
