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
  `MvPolynomial.X`), and its constants `R ↪ R[x₀, …, xₙ₋₁]` (Mathlib `MvPolynomial.C`);
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

/-- `ℕ ⊆ ℕ∞ ∪ {-∞}`. -/
def naturalsDimensions : naturals ⟶ dimensions :=
  TypeCat.ofHom (fun k : ℕ => ((k : ℕ∞) : WithBot ℕ∞))

theorem naturalsDimensions_mono : Mono naturalsDimensions :=
  NumberSystems.mono_of_injective _ (WithBot.coe_injective.comp fun _ _ h => ENat.natCast_inj.mp h)

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

normalized_registry .inclusion
  { id := ⟨"incl.sets.naturals_krull_dimensions"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.naturals"⟩, super := ⟨"obj.sets.krull_dimensions"⟩
    declaration := `CasCatalogue.Algebra.MvPolynomials.naturalsDimensions
    mono := `CasCatalogue.Algebra.MvPolynomials.naturalsDimensions_mono }

normalized_registry .morphism
  { id := ⟨"mor.sets.krull_dimension"⟩, category := CategoryId.sets, name := "dimension"
    declaration := `CasCatalogue.Algebra.MvPolynomials.dimension }

end CasCatalogue
