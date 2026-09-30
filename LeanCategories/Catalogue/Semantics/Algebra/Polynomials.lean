/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Ring
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Polynomials (SPEC.md, "Polynomials")

For a commutative ring `R`, `R[x]` is the set of polynomials over `R` (Mathlib `Polynomial R`),
refined by the ring `R[x]`, with
* its generator `x : 1 → R[x]` (Mathlib `Polynomial.X`), its constants
  `R ↪ R[x]` (Mathlib `Polynomial.C`), and
* its application `R[x] × A → A` at an `R`-algebra `A`, `(p, a) ↦ p(a)` (Mathlib
  `Polynomial.aeval`).

Functions of polynomials, as named morphism families of `Sets` over their rings:
* `deg : R[x] → ℕ ∪ {-∞}` (Mathlib `Polynomial.degree`; `deg 0 = -∞`);
* `R[x] ∖ {0} ↪ R[x]`, the nonzero polynomials; a polynomial is in `R[x] ∖ {0}` only with the
  evidence that it is nonzero;
* `factors : R[x] ∖ {0} → 𝒫_fin(R[x])`, the normalized irreducible factors over a unique
  factorization domain (Mathlib `UniqueFactorizationMonoid.normalizedFactors`). The zero
  polynomial has no factorization into irreducibles, so `0` is not in the domain (Mathlib's
  `normalizedFactors 0 = 0` is a convention, LC-14);
* `roots : R[x] ∖ {0} → 𝒫_fin(R)`, the roots in a domain `R` (Mathlib `Polynomial.roots`),
  finitely many for a nonzero polynomial. Every element of `R` is a root of `0`, so `0` is not in
  the domain (Mathlib's `roots 0 = ∅` is a convention, LC-14);
* `map : R[x] → S[x]` along an `R`-algebra `S` (Mathlib `Polynomial.map (algebraMap R S)`).
-/

open CategoryTheory Polynomial

namespace CasCatalogue.Algebra.Polynomials

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- `R[x]`. -/
abbrev polynomials (R : Type) [CommRing R] : SetsCat.{0} := Polynomial R

/-- The variable `x ∈ R[x]`. -/
noncomputable def generator (R : Type) [CommRing R] : fin 1 ⟶ polynomials R :=
  TypeCat.ofHom fun _ => X

/-- The constants `R ↪ R[x]` (Mathlib `Polynomial.C`), injective. -/
noncomputable def coefficients (R : Type) [CommRing R] : (R : SetsCat.{0}) ⟶ polynomials R :=
  TypeCat.ofHom (C : R →+* Polynomial R)

/-- `(p, a) ↦ p(a)`, `R[x] × A → A`. -/
noncomputable def evaluation (R A : Type) [CommRing R] [CommRing A] [Algebra R A] :
    (polynomials R × A : SetsCat.{0}) ⟶ (A : SetsCat.{0}) :=
  TypeCat.ofHom fun p => aeval p.2 p.1

/-- `R[x]` as a ring. -/
noncomputable abbrev ringPolynomials (R : Type) [CommRing R] : LeanCategories.Algebra.Rings.{0} :=
  RingCat.of (Polynomial R)

/-- The underlying set of the ring `R[x]` is `R[x]`. -/
def ringPolynomialsIdentification (R : Type) [CommRing R] :
    (polynomials R : SetsCat.{0}) ≅ polynomials R :=
  Iso.refl _

/-- `ℕ ∪ {-∞}`, the degrees. -/
abbrev degrees : SetsCat.{0} := WithBot ℕ

/-- `k ∈ ℕ ∪ {-∞}`. -/
def naturalsDegrees : naturals ⟶ degrees := TypeCat.ofHom (fun k : ℕ => (k : WithBot ℕ))

theorem naturalsDegrees_mono : Mono naturalsDegrees :=
  NumberSystems.mono_of_injective _ WithBot.coe_injective

/-- `deg : R[x] → ℕ ∪ {-∞}`. -/
noncomputable def degree (R : Type) [CommRing R] : (polynomials R : SetsCat.{0}) ⟶ degrees :=
  TypeCat.ofHom Polynomial.degree

/-- `R[x] ∖ {0}`, the nonzero polynomials. -/
abbrev nonzeroPolynomials (R : Type) [CommRing R] : SetsCat.{0} := {p : Polynomial R // p ≠ 0}

/-- `R[x] ∖ {0} ↪ R[x]`. -/
def nonzeroPolynomialsInclusion (R : Type) [CommRing R] :
    nonzeroPolynomials R ⟶ polynomials R :=
  TypeCat.ofHom Subtype.val

/-- The nonzero polynomial `p`, with the evidence that `p ≠ 0`. -/
def admitNonzeroPolynomial (R : Type) [CommRing R] (p : Polynomial R) (h : p ≠ 0) :
    fin 1 ⟶ nonzeroPolynomials R :=
  TypeCat.ofHom fun _ => ⟨p, h⟩

open Lean Elab Tactic in
/-- Close each remaining goal, a closed arithmetic fact about coefficients or degrees
(`Units.closedArithmeticEvidence`). -/
meta def closeCoefficientGoals : TacticM Unit := do
  for goal in ← getUnsolvedGoals do
    setGoals [goal]
    CasCatalogue.Algebra.Units.closedArithmeticEvidence

open Lean Elab Tactic in
/-- Put a closed polynomial expression in normal form: coefficients reduced modulo the
characteristic of `ℤ/n`, and the expression expanded into a sum of monomials `c·xᵏ` with like
terms collected (commutative-ring normalization), so that cancelling leading terms disappear. -/
meta def normalizePolynomial : TacticM Unit := do
  evalTactic (← `(tactic| try reduce_mod_char))
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

open Lean Elab Tactic in
/-- The evidence that a closed polynomial `p ∈ R[x]` (an expression in `x`, constants `C r`,
numerals, `+`, `-`, `·`, `^` over a closed commutative ring `R`: `ℤ`, `ℚ`, `ℝ`, `ℂ`, `ℤ/n`) is
nonzero: a polynomial is nonzero exactly when it has a degree `d ∈ ℕ`, i.e. a nonzero leading
coefficient. The degree is read off the expression, and, when its naive leading terms cancel,
off its normal form. It fails on the zero polynomial. -/
meta def nonzeroPolynomialEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "R[x] ∖ {0}" <| CasCatalogue.Evidence.closeByFirst
    m!"the polynomial is not established to be nonzero"
    [nonzeroByDegree, do normalizePolynomial; nonzeroByDegree]

open Classical in
/-- The normalized irreducible factors `R[x] ∖ {0} → 𝒫_fin(R[x])`. -/
noncomputable def factors (R : Type) [CommRing R] [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] :
    nonzeroPolynomials R ⟶ Foundation.FiniteSubsets.finiteSubsets (Polynomial R) :=
  TypeCat.ofHom fun p => (UniqueFactorizationMonoid.normalizedFactors p.1).toFinset

open Classical in
/-- The roots `R[x] ∖ {0} → 𝒫_fin(R)`, finitely many for a nonzero polynomial over a domain `R`
(Mathlib `Polynomial.roots`, `Polynomial.mem_roots`). -/
noncomputable def roots (R : Type) [CommRing R] [IsDomain R] :
    nonzeroPolynomials R ⟶ Foundation.FiniteSubsets.finiteSubsets R :=
  TypeCat.ofHom fun p => p.1.roots.toFinset

/-- The roots of a nonzero `p` are exactly the `a` with `p(a) = 0`. -/
theorem mem_roots (R : Type) [CommRing R] [IsDomain R] (p : nonzeroPolynomials R) (a : R) :
    a ∈ ConcreteCategory.hom (C := Type) (roots R) p ↔ IsRoot p.1 a := by
  simp [roots, Polynomial.mem_roots p.2]

/-- `map : R[x] → S[x]` along `R → S`. -/
noncomputable def map (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    (polynomials R : SetsCat.{0}) ⟶ polynomials S :=
  TypeCat.ofHom (Polynomial.map (algebraMap R S))

end CasCatalogue.Algebra.Polynomials

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.polynomials"⟩, category := CategoryId.sets, name := "Poly"
    declaration := `CasCatalogue.Algebra.Polynomials.polynomials
    generator := some `CasCatalogue.Algebra.Polynomials.generator
    application := some `CasCatalogue.Algebra.Polynomials.evaluation
    constants := some `CasCatalogue.Algebra.Polynomials.coefficients }

normalized_registry .object
  { id := ⟨"obj.rings.polynomials"⟩, category := CategoryId.rings, name := "Poly"
    declaration := `CasCatalogue.Algebra.Polynomials.ringPolynomials
    refines := some
      { base := ⟨"obj.sets.polynomials"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.Polynomials.ringPolynomialsIdentification } }

normalized_registry .object
  { id := ⟨"obj.sets.degrees"⟩, category := CategoryId.sets, name := "ℕ∪{-∞}"
    declaration := `CasCatalogue.Algebra.Polynomials.degrees }

normalized_registry .inclusion
  { id := ⟨"incl.sets.naturals_degrees"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.naturals"⟩, super := ⟨"obj.sets.degrees"⟩
    declaration := `CasCatalogue.Algebra.Polynomials.naturalsDegrees
    mono := `CasCatalogue.Algebra.Polynomials.naturalsDegrees_mono }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_degree"⟩, category := CategoryId.sets, name := "deg"
    declaration := `CasCatalogue.Algebra.Polynomials.degree }

normalized_registry .object
  { id := ⟨"obj.sets.nonzero_polynomials"⟩, category := CategoryId.sets, name := "Poly∖0"
    declaration := `CasCatalogue.Algebra.Polynomials.nonzeroPolynomials
    inclusion := some `CasCatalogue.Algebra.Polynomials.nonzeroPolynomialsInclusion
    admission := some `CasCatalogue.Algebra.Polynomials.admitNonzeroPolynomial
    evidence := some `CasCatalogue.Algebra.Polynomials.nonzeroPolynomialEvidence }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_factors"⟩, category := CategoryId.sets, name := "factors"
    declaration := `CasCatalogue.Algebra.Polynomials.factors }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_roots"⟩, category := CategoryId.sets, name := "roots"
    declaration := `CasCatalogue.Algebra.Polynomials.roots }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_map"⟩, category := CategoryId.sets, name := "map"
    declaration := `CasCatalogue.Algebra.Polynomials.map }

end CasCatalogue
