/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ArithmeticPlace
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Arithmetic bases

A Dedekind domain does not by itself say which places lie outside its spectrum. A number ring
has archimedean places; a ring of `S`-integers has those together with the inverted primes; the
coordinate ring of an affine curve has the points removed to make it affine. All three carry the
same shape of data: an integral model together with a distinguished set of places carrying their
own local coefficient rings.

`ArithmeticBase` is that data, and `Place` is one index type covering both kinds of place, so a
lattice is realized over a single index rather than over two unrelated ones. The number field
case is an instance, and its places match the `ArithmeticPlace` already in use.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsDedekindDomain NumberField
open scoped NumberField

namespace LeanCategories.Lattices.Valued

universe u

/-- An integral model together with the places lying outside its spectrum.

The height-one points of `R` carry the remaining places, so `Place` below is the full index.
Coefficient rings are bundled as objects of `CommRingCat` so that the family carries its own
ring structures. -/
class ArithmeticBase (R : Type u) (K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] where
  /-- The places not carried by a height-one point of `R`. -/
  DistinguishedPlace : Type u
  /-- The local coefficient ring used at a distinguished place. -/
  distinguishedCoefficient : DistinguishedPlace → CommRingCat.{u}
  /-- Each distinguished coefficient ring receives the base. -/
  distinguishedAlgebra : ∀ v, Algebra R (distinguishedCoefficient v)

namespace ArithmeticBase

variable (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [ArithmeticBase R K]

/-- Every place of the base: a height-one point of `R`, or a distinguished place. -/
abbrev Place := HeightOneSpectrum R ⊕ DistinguishedPlace (R := R) (K := K)

/-- The local coefficient ring at a place, bundled with its ring structure. Height-one points
use the completed local integers; distinguished places use their own coefficient ring. -/
abbrev coefficient : Place R K → CommRingCat.{u}
  | Sum.inl v => CommRingCat.of (v.adicCompletionIntegers K)
  | Sum.inr v => distinguishedCoefficient (R := R) (K := K) v

/-- A number ring is an arithmetic base whose distinguished places are the archimedean ones. -/
instance numberFieldArithmeticBase (F : Type u) [Field F] [NumberField F] :
    ArithmeticBase (𝓞 F) F where
  DistinguishedPlace := InfinitePlace F
  distinguishedCoefficient v := CommRingCat.of v.Completion
  distinguishedAlgebra _ := inferInstance

/-- For a number field the places of the arithmetic base are the arithmetic places already in
use, after identifying finite places with height-one points. -/
def numberFieldPlaceEquiv (F : Type u) [Field F] [NumberField F] :
    Place (𝓞 F) F ≃ ArithmeticPlace F :=
  Equiv.sumCongr (ArithmeticPlace.finiteEquivHeightOneSpectrum F).symm (Equiv.refl _)

end ArithmeticBase

end LeanCategories.Lattices.Valued
