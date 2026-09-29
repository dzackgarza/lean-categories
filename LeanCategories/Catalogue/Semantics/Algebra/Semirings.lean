/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.Algebra.Category.Ring.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Catalogue

@[expose] public section

/-!
# Semirings, and `ℕ` (SPEC.md, "Set comprehensions": `{2n | n ∈ ℕ}`)

`Semirings` (Mathlib `SemiRingCat`) with its underlying sets; `ℕ` is refined by the semiring `ℕ`,
whose operations are `+`, `·` and `^k`. The rings `ℤ, ℚ, ℝ, ℂ` are refined in `Rings` only, so each
operation on their elements has one owner.
-/

open CategoryTheory

namespace CasCatalogue

namespace CategoryId
def semirings : CategoryId := ⟨"cat.semirings"⟩
end CategoryId

namespace FunctorId
def semiringsForget : FunctorId := ⟨"fun.semirings.forget"⟩
end FunctorId

namespace Algebra.Semirings

open CasCatalogue.Foundation.Objects CasCatalogue.Foundation.PowerSets

universe u

def SemiringsExpr : CategoryExpr := .atom CategoryId.semirings

/-- Semirings. -/
def Semirings : LeanCategories.ObjCat.{u + 1, u} := Cat.of SemiRingCat.{u}

noncomputable def semiringsRealization : CategoryRealization SemiringsExpr Semirings.{u} := {}

/-- The underlying set of a semiring. -/
def semiringsForget : Semirings.{u} ⟶ SetsCat.{u} := (forget SemiRingCat.{u}).toCatHom

def SemiringsForgetExpr : FunctorExpr SemiringsExpr Foundation.Sets :=
  .atomic FunctorId.semiringsForget

noncomputable def semiringsForgetRealization :
    FunctorRealization SemiringsForgetExpr Semirings.{u} SetsCat.{u} semiringsForget.toFunctor :=
  { sourceRealization := semiringsRealization
    targetRealization := CasCatalogue.Foundation.CatalogueRegistration.setsRealization }

/-- A semiring as a `SemiRingCat`, and its underlying type. -/
abbrev asSemiring (R : Semirings.{0}) : SemiRingCat.{0} := R
abbrev semiringCarrier (R : Semirings.{0}) : Type := asSemiring R

/-- Addition. -/
def add (R : Semirings.{0}) :
    (semiringCarrier R × semiringCarrier R : SetsCat.{0}) ⟶ (semiringCarrier R : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 + p.2
/-- Multiplication. -/
def mul (R : Semirings.{0}) :
    (semiringCarrier R × semiringCarrier R : SetsCat.{0}) ⟶ (semiringCarrier R : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 * p.2
/-- The power `x ↦ x^k`. -/
def pow (R : Semirings.{0}) (k : ℕ) :
    (semiringCarrier R : SetsCat.{0}) ⟶ (semiringCarrier R : SetsCat.{0}) :=
  TypeCat.ofHom fun x => x ^ k

/-- `ℕ` as a semiring; its underlying set is `ℕ`. -/
abbrev semiringNaturals : Semirings.{0} := SemiRingCat.of ℕ
def semiringNaturalsIdentification : (naturals : SetsCat.{0}) ≅ naturals := Iso.refl _

end Algebra.Semirings

open Algebra.Semirings

normalized_registry .category
  { id := CategoryId.semirings, name := "Semirings"
    declaration := `CasCatalogue.Algebra.Semirings.Semirings
    expression := SemiringsExpr
    realization := `CasCatalogue.Algebra.Semirings.semiringsRealization }

normalized_registry .functor
  { id := FunctorId.semiringsForget, source := SemiringsExpr, target := Foundation.Sets
    declaration := `CasCatalogue.Algebra.Semirings.semiringsForget
    realization := `CasCatalogue.Algebra.Semirings.semiringsForgetRealization
    expression := SemiringsForgetExpr, structural := true }

normalized_registry .object
  { id := ⟨"obj.semirings.naturals"⟩, category := CategoryId.semirings, name := "ℕ"
    declaration := `CasCatalogue.Algebra.Semirings.semiringNaturals
    refines := some
      { base := ⟨"obj.sets.naturals"⟩, route := #[.functor FunctorId.semiringsForget]
        identification := `CasCatalogue.Algebra.Semirings.semiringNaturalsIdentification } }

normalized_registry .operation
  { id := ⟨"op.semirings.add"⟩, category := CategoryId.semirings, name := "+", arity := 2
    declaration := `CasCatalogue.Algebra.Semirings.add }
normalized_registry .operation
  { id := ⟨"op.semirings.mul"⟩, category := CategoryId.semirings, name := "·", arity := 2
    declaration := `CasCatalogue.Algebra.Semirings.mul }
normalized_registry .operation
  { id := ⟨"op.semirings.pow"⟩, category := CategoryId.semirings, name := "^", arity := 1
    numerals := 1, declaration := `CasCatalogue.Algebra.Semirings.pow }

end CasCatalogue
