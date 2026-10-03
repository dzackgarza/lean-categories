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
* the coordinate comparison and its inverse are the underlying maps of Mathlib's
  `R[x]`-linear equivalence; `dx` is the differential of the polynomial generator;
* `derivative : R[x] → R[x]` is `d/dx` (Mathlib `Polynomial.derivative`);
* `∫ : Ω¹ → 𝒫(R[x])` sends a differential `ω` to its primitives `{g | d g = ω}`, a coset of the
  kernel of `d`, the constants.
-/

open CategoryTheory Polynomial

namespace CasCatalogue.Algebra.Differentials

open CasCatalogue.Algebra.Polynomials CasCatalogue.Foundation.PowerSets

/-- `Ω¹_{R[x]/R}`. -/
abbrev differentials (R : CommRingCat.{0}) : SetsCat.{0} := Ω[Polynomial R⁄R]

/-- The canonical `R[x]`-linear coordinate comparison for relative differentials.
This is Mathlib's `KaehlerDifferential.polynomialEquiv`, valid over every commutative ring.
LC-09 search: the corpus queries `polynomialEquiv` and
`polynomial_D_apply or polynomialEquiv_D or polynomialEquiv_symm` locate this comparison
and its construction laws in `Mathlib/RingTheory/Kaehler/Polynomial.lean`. -/
noncomputable def coordinateEquiv (R : CommRingCat.{0}) :
    Ω[Polynomial R⁄R] ≃ₗ[Polynomial R] Polynomial R :=
  KaehlerDifferential.polynomialEquiv R

/-- The coefficient of a relative differential in the basis `dx`. -/
noncomputable def coordinate (R : CommRingCat.{0}) :
    differentials R ⟶ polynomials R :=
  TypeCat.ofHom (coordinateEquiv R)

/-- The differential with the given coefficient of `dx`. -/
noncomputable def fromCoordinate (R : CommRingCat.{0}) :
    (polynomials R : SetsCat.{0}) ⟶ differentials R :=
  TypeCat.ofHom (coordinateEquiv R).symm

/-- The distinguished differential `dx = d(x)`. -/
noncomputable def dx (R : CommRingCat.{0}) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ differentials R :=
  TypeCat.ofHom fun _ => KaehlerDifferential.D R (Polynomial R) X

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

/-- Coordinate extraction and reconstruction are inverse. -/
@[simp] theorem coordinate_fromCoordinate (R : CommRingCat.{0}) (p : Polynomial R) :
    coordinate R (fromCoordinate R p) = p :=
  (coordinateEquiv R).apply_symm_apply p

/-- Every relative differential is recovered from its coefficient. -/
@[simp] theorem fromCoordinate_coordinate (R : CommRingCat.{0})
    (ω : Ω[Polynomial R⁄R]) : fromCoordinate R (coordinate R ω) = ω :=
  (coordinateEquiv R).symm_apply_apply ω

/-- Reconstruction is precisely multiplication by the distinguished `dx`. -/
theorem fromCoordinate_eq_scale_dx (R : CommRingCat.{0}) (p : Polynomial R)
    (u : CasCatalogue.Foundation.Objects.fin 1) :
    fromCoordinate R p = scale R (p, dx R u) :=
  KaehlerDifferential.polynomialEquiv_symm R p

/-- The universal relative differential has coefficient the formal derivative. -/
@[simp] theorem coordinate_differential (R : CommRingCat.{0}) (p : Polynomial R) :
    coordinate R (differential R p) = derivative R p :=
  KaehlerDifferential.polynomialEquiv_D R p

/-- `d(p) = p' dx`, with the universal derivation retained as the definition of `d`. -/
theorem differential_eq_scale_dx (R : CommRingCat.{0}) (p : Polynomial R)
    (u : CasCatalogue.Foundation.Objects.fin 1) :
    differential R p = scale R (derivative R p, dx R u) :=
  KaehlerDifferential.polynomial_D_apply R p

/-- A primitive of `p dx` is exactly a polynomial with derivative `p`. -/
theorem mem_primitives_fromCoordinate (R : CommRingCat.{0}) (p g : Polynomial R) :
    g ∈ primitives R (fromCoordinate R p) ↔ derivative R g = p := by
  change KaehlerDifferential.D R (Polynomial R) g = (coordinateEquiv R).symm p ↔ _
  constructor
  · intro h
    have h' := congrArg (coordinateEquiv R) h
    simpa [coordinateEquiv, derivative] using h'
  · intro h
    apply (coordinateEquiv R).injective
    simpa [coordinateEquiv, derivative] using h

end CasCatalogue.Algebra.Differentials

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.kaehler_polynomials"⟩, category := CategoryId.sets, name := "Ω¹"
    declaration := `CasCatalogue.Algebra.Differentials.differentials }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_differential"⟩, category := CategoryId.sets, name := "d"
    declaration := `CasCatalogue.Algebra.Differentials.differential }

normalized_registry .morphism
  { id := ⟨"mor.sets.kaehler_coordinate"⟩, category := CategoryId.sets, name := "coordinate"
    declaration := `CasCatalogue.Algebra.Differentials.coordinate }

normalized_registry .morphism
  { id := ⟨"mor.sets.kaehler_from_coordinate"⟩, category := CategoryId.sets
    name := "fromCoordinate"
    declaration := `CasCatalogue.Algebra.Differentials.fromCoordinate }

normalized_registry .morphism
  { id := ⟨"mor.sets.kaehler_dx"⟩, category := CategoryId.sets, name := "dx"
    declaration := `CasCatalogue.Algebra.Differentials.dx }

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
