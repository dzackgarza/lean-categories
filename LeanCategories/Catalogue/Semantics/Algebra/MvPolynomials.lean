/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Polynomials in several variables, and Krull dimension (SPEC.md, "Ellipses")

For a commutative ring `R`, `R[x₀, …, xₙ₋₁]` is the set of polynomials in `n` variables (Mathlib
`MvPolynomial (Fin n) R`), refined by the ring of that name, with
* its variables `xᵢ : 1 → R[x₀, …, xₙ₋₁]`, a generator indexed by `i < n` (Mathlib
  `MvPolynomial.X`), its numerals and its constants `R ↪ R[x₀, …, xₙ₋₁]` (Mathlib `MvPolynomial.C`);
* the total degree `R[x₀, …, xₙ₋₁] → ℕ` (Mathlib `MvPolynomial.totalDegree`).

The Krull dimension of a commutative ring `A` is an invariant of the object, not of its elements:
the element `dim A : 1 → ℕ∞ ∪ {-∞}` of the set of dimensions (Mathlib `ringKrullDim`).
-/

open CategoryTheory

namespace CasCatalogue.Algebra.MvPolynomials

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- `R[x₀, …, xₙ₋₁]`. -/
abbrev mvPolynomials (n : ℕ) (R : Type) [CommRing R] : SetsCat.{0} := MvPolynomial (Fin n) R

/-- The variable `xᵢ`. -/
noncomputable def var (n : ℕ) (R : Type) [CommRing R] (i : Fin n) :
    fin 1 ⟶ mvPolynomials n R :=
  TypeCat.ofHom fun _ => MvPolynomial.X i

/-- The numeral `k`. -/
noncomputable def numeral (n : ℕ) (R : Type) [CommRing R] (k : ℕ) : Option (mvPolynomials n R) :=
  some (k : MvPolynomial (Fin n) R)

/-- The constants `R ↪ R[x₀, …, xₙ₋₁]`. -/
noncomputable def constants (n : ℕ) (R : Type) [CommRing R] :
    (R : SetsCat.{0}) ⟶ mvPolynomials n R :=
  TypeCat.ofHom fun r => MvPolynomial.C r

/-- `R[x₀, …, xₙ₋₁]` as a ring. -/
noncomputable abbrev ringMvPolynomials (n : ℕ) (R : Type) [CommRing R] :
    LeanCategories.Algebra.Rings.{0} :=
  RingCat.of (MvPolynomial (Fin n) R)

/-- The underlying set of the ring `R[x₀, …, xₙ₋₁]` is `R[x₀, …, xₙ₋₁]`. -/
def ringMvPolynomialsIdentification (n : ℕ) (R : Type) [CommRing R] :
    (mvPolynomials n R : SetsCat.{0}) ≅ mvPolynomials n R :=
  Iso.refl _

/-- The total degree. -/
def totalDegree (n : ℕ) (R : Type) [CommRing R] : mvPolynomials n R ⟶ naturals :=
  TypeCat.ofHom fun p => p.totalDegree

/-- `ℕ∞ ∪ {-∞}`, the Krull dimensions. -/
abbrev dimensions : SetsCat.{0} := WithBot ℕ∞

/-- The numeral `k ∈ ℕ∞ ∪ {-∞}`. -/
def dimensionsElement (k : ℕ) : Option dimensions := some (k : WithBot ℕ∞)

/-- The Krull dimension of a commutative ring `A`. -/
noncomputable def dimension (A : Type) [CommRing A] : fin 1 ⟶ dimensions :=
  TypeCat.ofHom fun _ => ringKrullDim A

end CasCatalogue.Algebra.MvPolynomials

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.mv_polynomials"⟩, category := CategoryId.sets, name := "MvPoly"
    declaration := `CasCatalogue.Algebra.MvPolynomials.mvPolynomials
    generator := some `CasCatalogue.Algebra.MvPolynomials.var
    constants := some `CasCatalogue.Algebra.MvPolynomials.constants }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.mv_polynomials"⟩, object := ⟨"obj.sets.mv_polynomials"⟩
    denotation := `CasCatalogue.Algebra.MvPolynomials.numeral }

normalized_registry .object
  { id := ⟨"obj.rings.mv_polynomials"⟩, category := CategoryId.rings, name := "MvPoly"
    declaration := `CasCatalogue.Algebra.MvPolynomials.ringMvPolynomials
    refines := some
      { base := ⟨"obj.sets.mv_polynomials"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.MvPolynomials.ringMvPolynomialsIdentification } }

normalized_registry .morphism
  { id := ⟨"mor.sets.mv_total_degree"⟩, category := CategoryId.sets, name := "total_degree"
    declaration := `CasCatalogue.Algebra.MvPolynomials.totalDegree }

normalized_registry .object
  { id := ⟨"obj.sets.krull_dimensions"⟩, category := CategoryId.sets, name := "ℕ∞∪{-∞}"
    declaration := `CasCatalogue.Algebra.MvPolynomials.dimensions }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.krull_dimensions"⟩, object := ⟨"obj.sets.krull_dimensions"⟩
    denotation := `CasCatalogue.Algebra.MvPolynomials.dimensionsElement }

normalized_registry .morphism
  { id := ⟨"mor.sets.krull_dimension"⟩, category := CategoryId.sets, name := "dimension"
    declaration := `CasCatalogue.Algebra.MvPolynomials.dimension }

end CasCatalogue
