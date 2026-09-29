/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Polynomials (SPEC.md, "Polynomials")

For a commutative ring `R`, `R[x]` is the set of polynomials over `R` (Mathlib `Polynomial R`),
refined by the ring `R[x]`, with
* its generator `x : 1 → R[x]` (Mathlib `Polynomial.X`), its numerals `k ∈ R[x]`, its constants
  `R ↪ R[x]` (Mathlib `Polynomial.C`), and
* its application `R[x] × A → A` at an `R`-algebra `A`, `(p, a) ↦ p(a)` (Mathlib
  `Polynomial.aeval`).

Functions of polynomials, as named morphism families of `Sets` over their rings:
* `deg : R[x] → ℕ ∪ {-∞}` (Mathlib `Polynomial.degree`; `deg 0 = -∞`);
* `factors : R[x] → 𝒫(R[x])`, the normalized irreducible factors over a unique factorization
  domain (Mathlib `UniqueFactorizationMonoid.normalizedFactors`);
* `roots : R[x] → 𝒫(R)`, the roots in a domain `R` (Mathlib `Polynomial.roots`);
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

/-- The constant polynomial `k ∈ R[x]`. -/
noncomputable def constant (R : Type) [CommRing R] (k : ℕ) : Option (polynomials R) :=
  some (k : Polynomial R)

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
def degreesElement (k : ℕ) : Option degrees := some (k : WithBot ℕ)

/-- `deg : R[x] → ℕ ∪ {-∞}`. -/
noncomputable def degree (R : Type) [CommRing R] : (polynomials R : SetsCat.{0}) ⟶ degrees :=
  TypeCat.ofHom Polynomial.degree

/-- The normalized irreducible factors `R[x] → 𝒫(R[x])`. -/
noncomputable def factors (R : Type) [CommRing R] [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R] :
    (polynomials R : SetsCat.{0}) ⟶ powerSet (Polynomial R) :=
  TypeCat.ofHom fun p => {q | q ∈ UniqueFactorizationMonoid.normalizedFactors p}

/-- The roots `R[x] → 𝒫(R)`. -/
noncomputable def roots (R : Type) [CommRing R] [IsDomain R] :
    (polynomials R : SetsCat.{0}) ⟶ powerSet R :=
  TypeCat.ofHom fun p => {a | a ∈ p.roots}

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

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.polynomials"⟩, object := ⟨"obj.sets.polynomials"⟩
    denotation := `CasCatalogue.Algebra.Polynomials.constant }

normalized_registry .object
  { id := ⟨"obj.rings.polynomials"⟩, category := CategoryId.rings, name := "Poly"
    declaration := `CasCatalogue.Algebra.Polynomials.ringPolynomials
    refines := some
      { base := ⟨"obj.sets.polynomials"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.Polynomials.ringPolynomialsIdentification } }

normalized_registry .object
  { id := ⟨"obj.sets.degrees"⟩, category := CategoryId.sets, name := "ℕ∪{-∞}"
    declaration := `CasCatalogue.Algebra.Polynomials.degrees }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.degrees"⟩, object := ⟨"obj.sets.degrees"⟩
    denotation := `CasCatalogue.Algebra.Polynomials.degreesElement }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_degree"⟩, category := CategoryId.sets, name := "deg"
    declaration := `CasCatalogue.Algebra.Polynomials.degree }

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
