/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Catalogue

@[expose] public section

/-!
# Semirings, and `ℕ` (SPEC.md, "Set comprehensions": `{2n | n ∈ ℕ}`)

`Semirings` (Mathlib `SemiRingCat`) with its underlying sets; `ℕ` is refined by the semiring `ℕ`,
whose operations are `+`, `·` and `^k`; primality `ℕ → Ω` is a predicate on its elements (Mathlib
`Nat.Prime`), and the factorization of `n = ∏ pᵉᵖ` is given by its prime factors `ℕ → 𝒫_fin(ℕ)` and the
multiplicities `(n, p) ↦ eₚ` (Mathlib `Nat.primeFactors`, `Nat.factorization`). The rings `ℤ, ℚ, ℝ, ℂ` are refined in `Rings` only, so each
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

/-- The numeral `k` of a semiring `S`: the image of `k` under the unique semiring map `ℕ → S` out of
the initial semiring (Mathlib `Nat.castRingHom`), LC-15; for `S = ℕ`, `k` itself. -/
def semiringNumeral (S : Semirings.{0}) (k : ℕ) : fin 1 ⟶ (semiringCarrier S : SetsCat.{0}) :=
  TypeCat.ofHom fun _ => Nat.castRingHom (asSemiring S) k

/-- `ℕ` as a semiring; its underlying set is `ℕ`. -/
abbrev semiringNaturals : Semirings.{0} := SemiRingCat.of ℕ
/-- `n ↦ n is prime`, `ℕ → Ω`. -/
def isPrime : naturals ⟶ omega := TypeCat.ofHom fun n => Nat.Prime n

/-- The prime factors of `n` (none for `n = 0, 1`). -/
def primeFactors : naturals ⟶ Foundation.FiniteSubsets.finiteSubsets ℕ :=
  TypeCat.ofHom fun n => n.primeFactors

/-- `(n, p) ↦` the exponent of `p` in `n` (`0` unless `p` is a prime factor). -/
noncomputable def multiplicity : (naturals × naturals : SetsCat.{0}) ⟶ naturals :=
  TypeCat.ofHom fun p => p.1.factorization p.2

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

normalized_registry .numeral
  { id := ⟨"num.semirings"⟩, over := some CategoryId.semirings
    declaration := `CasCatalogue.Algebra.Semirings.semiringNumeral }

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

normalized_registry .morphism
  { id := ⟨"mor.sets.nat_is_prime"⟩, category := CategoryId.sets, name := "is_prime"
    declaration := `CasCatalogue.Algebra.Semirings.isPrime }

normalized_registry .morphism
  { id := ⟨"mor.sets.nat_prime_factors"⟩, category := CategoryId.sets, name := "prime_factors"
    declaration := `CasCatalogue.Algebra.Semirings.primeFactors }

normalized_registry .morphism
  { id := ⟨"mor.sets.nat_multiplicity"⟩, category := CategoryId.sets, name := "multiplicity"
    declaration := `CasCatalogue.Algebra.Semirings.multiplicity }

end CasCatalogue
