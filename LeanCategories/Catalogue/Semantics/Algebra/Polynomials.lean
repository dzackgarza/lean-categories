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
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Data.Int.CharZero
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import LeanCategories.Catalogue.Semantics.Algebra.PolynomialEvidence
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
* `map : R[x] → S[x]` along an `R`-algebra `S` (Mathlib `Polynomial.map f.hom`).
-/

open CategoryTheory Polynomial

namespace CasCatalogue.Algebra.Polynomials

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- `R[x]`. -/
abbrev polynomials (R : CommRingCat.{0}) : SetsCat.{0} := Polynomial R

/-- The variable `x ∈ R[x]`. -/
noncomputable def generator (R : CommRingCat.{0}) : fin 1 ⟶ polynomials R :=
  TypeCat.ofHom fun _ => X

/-- The constants `R ↪ R[x]` (Mathlib `Polynomial.C`), injective. -/
noncomputable def coefficients (R : CommRingCat.{0}) : (R : SetsCat.{0}) ⟶ polynomials R :=
  TypeCat.ofHom (C : R →+* Polynomial R)

/-- `(p, a) ↦ p(a)`, `R[x] × A → A`. -/
noncomputable def evaluation (R : CommRingCat.{0}) (A : Under R) :
    (polynomials R × A : SetsCat.{0}) ⟶ (A : SetsCat.{0}) :=
  TypeCat.ofHom fun p => aeval p.2 p.1

/-- `R[x]` as a ring. -/
noncomputable abbrev ringPolynomials (R : CommRingCat.{0}) : LeanCategories.Algebra.Rings.{0} :=
  RingCat.of (Polynomial R)

/-- The underlying set of the ring `R[x]` is `R[x]`. -/
def ringPolynomialsIdentification (R : CommRingCat.{0}) :
    (polynomials R : SetsCat.{0}) ≅ polynomials R :=
  Iso.refl _

/-- `ℕ ∪ {-∞}`, the degrees. -/
abbrev degrees : SetsCat.{0} := WithBot ℕ

/-- `k ∈ ℕ ∪ {-∞}`. -/
def naturalsDegrees : naturals ⟶ degrees := TypeCat.ofHom (fun k : ℕ => (k : WithBot ℕ))

theorem naturalsDegrees_mono : Mono naturalsDegrees :=
  NumberSystems.mono_of_injective _ WithBot.coe_injective

/-- `deg : R[x] → ℕ ∪ {-∞}`. -/
noncomputable def degree (R : CommRingCat.{0}) : (polynomials R : SetsCat.{0}) ⟶ degrees :=
  TypeCat.ofHom Polynomial.degree

/-- `R[x] ∖ {0}`, the nonzero polynomials. -/
abbrev nonzeroPolynomials (R : CommRingCat.{0}) : SetsCat.{0} := {p : Polynomial R // p ≠ 0}

/-- `R[x] ∖ {0} ↪ R[x]`. -/
def nonzeroPolynomialsInclusion (R : CommRingCat.{0}) :
    nonzeroPolynomials R ⟶ polynomials R :=
  TypeCat.ofHom Subtype.val

/-- The nonzero polynomial `p`, with the evidence that `p ≠ 0`. -/
def admitNonzeroPolynomial (R : CommRingCat.{0}) (p : Polynomial R) (h : p ≠ 0) :
    fin 1 ⟶ nonzeroPolynomials R :=
  TypeCat.ofHom fun _ => ⟨p, h⟩

open Classical in
/-- The normalized irreducible factors `R[x] ∖ {0} → 𝒫_fin(R[x])`. -/
noncomputable def factors (R : CommRingCat.{0}) [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] :
    nonzeroPolynomials R ⟶ Foundation.FiniteSubsets.finiteSubsets (Polynomial R) :=
  TypeCat.ofHom fun p => (UniqueFactorizationMonoid.normalizedFactors p.1).toFinset

open Classical in
/-- The roots `R[x] ∖ {0} → 𝒫_fin(R)`, finitely many for a nonzero polynomial over a domain `R`
(Mathlib `Polynomial.roots`, `Polynomial.mem_roots`). -/
noncomputable def roots (R : CommRingCat.{0}) [IsDomain R] :
    nonzeroPolynomials R ⟶ Foundation.FiniteSubsets.finiteSubsets R :=
  TypeCat.ofHom fun p => p.1.roots.toFinset

/-- The roots of a nonzero `p` are exactly the `a` with `p(a) = 0`. -/
theorem mem_roots (R : CommRingCat.{0}) [IsDomain R] (p : nonzeroPolynomials R) (a : R) :
    a ∈ ConcreteCategory.hom (C := Type) (roots R) p ↔ IsRoot p.1 a := by
  simp [roots, Polynomial.mem_roots p.2]

/-- The existing finite root operation retains precisely its defining comprehension.
It is the same extent admitted by `FiniteSubsets.admit`, rather than a new root set. -/
theorem roots_extent (R : CommRingCat.{0}) [IsDomain R] (p : nonzeroPolynomials R) :
    (ConcreteCategory.hom (C := Type) (roots R) p : Set R) =
      {a | p.1.eval a = 0} := by
  ext a
  exact mem_roots R p a

/-- Admitting the root comprehension recovers exactly the existing finite-root value. -/
theorem admit_roots (R : CommRingCat.{0}) [IsDomain R] (p : nonzeroPolynomials R)
    (x : CasCatalogue.Foundation.Objects.fin 1) :
    ConcreteCategory.hom (C := Type)
      (Foundation.FiniteSubsets.admit R {a | p.1.eval a = 0}
        (Foundation.FiniteSubsets.finite_polynomial_zeros p.1 p.2)) x =
      ConcreteCategory.hom (C := Type) (roots R) p := by
  apply Finset.coe_injective
  exact (Set.Finite.coe_toFinset _).trans (roots_extent R p).symm

/-- `map : R[x] → S[x]` along `R → S`. -/
noncomputable def map (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (polynomials R : SetsCat.{0}) ⟶ polynomials S :=
  TypeCat.ofHom (Polynomial.map f.hom)

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
