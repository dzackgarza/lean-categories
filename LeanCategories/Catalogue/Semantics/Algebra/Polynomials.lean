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
public meta import LeanCategories.Catalogue.Registry.Semantic

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
* `factors : R[x] → 𝒫_fin(R[x])`, the normalized irreducible factors over a unique factorization
  domain (Mathlib `UniqueFactorizationMonoid.normalizedFactors`);
* `roots : R[x] → 𝒫_fin(R)`, the roots in a domain `R` (Mathlib `Polynomial.roots`);
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

open Classical in
/-- The normalized irreducible factors `R[x] → 𝒫_fin(R[x])`. -/
noncomputable def factors (R : Type) [CommRing R] [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] :
    (polynomials R : SetsCat.{0}) ⟶ Foundation.FiniteSubsets.finiteSubsets (Polynomial R) :=
  TypeCat.ofHom fun p => (UniqueFactorizationMonoid.normalizedFactors p).toFinset

open Classical in
/-- The roots `R[x] → 𝒫_fin(R)`, finitely many for a domain `R` (Mathlib `Polynomial.roots`). -/
noncomputable def roots (R : Type) [CommRing R] [IsDomain R] :
    (polynomials R : SetsCat.{0}) ⟶ Foundation.FiniteSubsets.finiteSubsets R :=
  TypeCat.ofHom fun p => p.roots.toFinset

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
