/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import Mathlib.RingTheory.Kaehler.Polynomial
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Differentials and primitives of polynomials (SPEC.md, "Differentials", "Indefinite integration")

For a commutative ring `R`:
* `Ω¹(R)` is the module of Kähler differentials `Ω¹_{R[x]/R}` (Mathlib `KaehlerDifferential`), the
  target of the universal `R`-derivation `d : R[x] → Ω¹_{R[x]/R}` (Mathlib `KaehlerDifferential.D`);
  `Ω¹_{R[x]/R} ≅ R[x] dx` with `d p = p' dx` (Mathlib `KaehlerDifferential.polynomialEquiv`,
  `polynomial_D_apply`);
* `• : R[x] × Ω¹ → Ω¹` is its module structure (`p dx`);
* `derivative : R[x] → R[x]` is `d/dx` (Mathlib `Polynomial.derivative`);
* `∫ : Ω¹ → 𝒫(R[x])` sends a differential `ω` to its primitives `{g | d g = ω}`, a coset of the
  kernel of `d`, the constants.
-/

open CategoryTheory Polynomial

namespace CasCatalogue.Algebra.Differentials

open CasCatalogue.Algebra.Polynomials CasCatalogue.Foundation.PowerSets

/-- `Ω¹_{R[x]/R}`. -/
abbrev differentials (R : CommRingCat.{0}) : SetsCat.{0} := Ω[Polynomial R⁄R]

/-- The universal derivation `d : R[x] → Ω¹_{R[x]/R}`. -/
noncomputable def differential (R : CommRingCat.{0}) :
    (polynomials R : SetsCat.{0}) ⟶ differentials R :=
  TypeCat.ofHom fun p => KaehlerDifferential.D R (Polynomial R) p

/-- The module structure `R[x] × Ω¹_{R[x]/R} → Ω¹_{R[x]/R}`, `(p, ω) ↦ p ω`. -/
noncomputable def scale (R : CommRingCat.{0}) :
    (polynomials R × differentials R : SetsCat.{0}) ⟶ differentials R :=
  TypeCat.ofHom fun p => p.1 • p.2

/-- `d/dx : R[x] → R[x]`. -/
noncomputable def derivative (R : CommRingCat.{0}) :
    (polynomials R : SetsCat.{0}) ⟶ polynomials R :=
  TypeCat.ofHom fun p => Polynomial.derivative p

/-- The primitives `∫ ω = {g | d g = ω}` of a differential. -/
noncomputable def primitives (R : CommRingCat.{0}) :
    differentials R ⟶ powerSet (Polynomial R) :=
  TypeCat.ofHom fun ω => {g | KaehlerDifferential.D R (Polynomial R) g = ω}

end CasCatalogue.Algebra.Differentials

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.kaehler_polynomials"⟩, category := CategoryId.sets, name := "Ω¹"
    declaration := `CasCatalogue.Algebra.Differentials.differentials }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_differential"⟩, category := CategoryId.sets, name := "d"
    declaration := `CasCatalogue.Algebra.Differentials.differential }

normalized_registry .morphism
  { id := ⟨"mor.sets.kaehler_scale"⟩, category := CategoryId.sets, name := "•"
    declaration := `CasCatalogue.Algebra.Differentials.scale }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_derivative"⟩, category := CategoryId.sets, name := "derivative"
    declaration := `CasCatalogue.Algebra.Differentials.derivative }

normalized_registry .morphism
  { id := ⟨"mor.sets.kaehler_primitives"⟩, category := CategoryId.sets, name := "∫"
    declaration := `CasCatalogue.Algebra.Differentials.primitives }

end CasCatalogue
