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
`Nat.Prime`). The factorization `n = ∏ pᵉᵖ` of a positive `n ∈ ℕ⁺ ↪ ℕ` (Mathlib `ℕ+`) is given by
its prime factors `ℕ⁺ → 𝒫_fin(ℙ)` and the multiplicities `ℕ⁺ × ℙ → ℕ`, `(n, p) ↦ eₚ`, where
`ℙ ↪ ℕ` are the primes (Mathlib `Nat.Primes`, `Nat.primeFactors`, `Nat.factorization`). `0` has no
factorization (every prime divides it, to every power), so it is not in the domain; Mathlib's
`primeFactors 0 = ∅` and `factorization 0 = 0` are conventions (LC-14). An exponent `eₚ` is defined
for a prime `p` only. The rings `ℤ, ℚ, ℝ, ℂ` are refined in `Rings` only, so each operation on
their elements has one owner.
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

/-- `ℕ⁺`, the positive naturals. -/
abbrev positiveNaturals : SetsCat.{0} := ℕ+

/-- `ℕ⁺ ↪ ℕ`. -/
def positiveNaturalsInclusion : positiveNaturals ⟶ naturals := TypeCat.ofHom PNat.val

/-- The positive natural `n`, with the evidence that `0 < n`. -/
def admitPositive (n : ℕ) (h : 0 < n) : fin 1 ⟶ positiveNaturals :=
  TypeCat.ofHom fun _ => ⟨n, h⟩

/-- `ℙ`, the primes. -/
abbrev primes : SetsCat.{0} := Nat.Primes

/-- `ℙ ↪ ℕ`. -/
def primesInclusion : primes ⟶ naturals := TypeCat.ofHom Subtype.val

/-- The prime `p`, with the evidence that `p` is prime. -/
def admitPrime (p : ℕ) (h : p.Prime) : fin 1 ⟶ primes := TypeCat.ofHom fun _ => ⟨p, h⟩

/-- The prime factors of `n ∈ ℕ⁺` (none for `n = 1`), `ℕ⁺ → 𝒫_fin(ℙ)`. -/
def primeFactors : positiveNaturals ⟶ Foundation.FiniteSubsets.finiteSubsets Nat.Primes :=
  TypeCat.ofHom fun n => ((n : ℕ).primeFactors.subtype Nat.Prime : Finset Nat.Primes)

/-- `(n, p) ↦ eₚ`, the exponent of the prime `p` in `n ∈ ℕ⁺` (`0` when `p ∤ n`). -/
noncomputable def multiplicity : (positiveNaturals × primes : SetsCat.{0}) ⟶ naturals :=
  TypeCat.ofHom fun p => (p.1 : ℕ).factorization p.2.1

/-- The prime factors of `n ∈ ℕ⁺` are the primes dividing it. -/
theorem mem_primeFactors (n : ℕ+) (p : Nat.Primes) :
    p ∈ ConcreteCategory.hom (C := Type) primeFactors n ↔ p.1 ∣ n := by
  obtain ⟨p, hp⟩ := p
  change (⟨p, hp⟩ : {q : ℕ // q.Prime}) ∈ (n : ℕ).primeFactors.subtype Nat.Prime ↔ _
  rw [Finset.mem_subtype, Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨hp, h, n.ne_zero⟩⟩

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

normalized_registry .object
  { id := ⟨"obj.sets.positive_naturals"⟩, category := CategoryId.sets, name := "ℕ⁺"
    declaration := `CasCatalogue.Algebra.Semirings.positiveNaturals
    inclusion := some `CasCatalogue.Algebra.Semirings.positiveNaturalsInclusion
    admission := some `CasCatalogue.Algebra.Semirings.admitPositive }

normalized_registry .object
  { id := ⟨"obj.sets.primes"⟩, category := CategoryId.sets, name := "ℙ"
    declaration := `CasCatalogue.Algebra.Semirings.primes
    inclusion := some `CasCatalogue.Algebra.Semirings.primesInclusion
    admission := some `CasCatalogue.Algebra.Semirings.admitPrime }

normalized_registry .morphism
  { id := ⟨"mor.sets.nat_prime_factors"⟩, category := CategoryId.sets, name := "prime_factors"
    declaration := `CasCatalogue.Algebra.Semirings.primeFactors }

normalized_registry .morphism
  { id := ⟨"mor.sets.nat_multiplicity"⟩, category := CategoryId.sets, name := "multiplicity"
    declaration := `CasCatalogue.Algebra.Semirings.multiplicity }

end CasCatalogue
