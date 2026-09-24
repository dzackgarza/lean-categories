/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Derived Hom representatives

Weibel, *An Introduction to Homological Algebra* (1994), Definition 10.7.2,
pp. 398--401 (FC05-C10-U081).

For `B : D⁺(C)`, choose a bounded-below cochain representative and then Mathlib's canonical
fibrant replacement in the injective model structure.  The resulting complex is degreewise
injective, so `Hom•(A,I_B)`, localized to `D(Ab)`, is the source-level object denoted
`RHom(A,B)`.  Independence of these choices, functoriality on the derived category, and the
right-derived universal property belong to the theorem layer.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A bounded-below cochain representative of an object of `D⁺(C)`.

The two `objPreimage` choices only select representatives of the two localization steps;
comparison of different choices is theorem-layer material. -/
noncomputable def rHomPlusRepresentative [HasDerivedCategory C]
    (B : DerivedCategory.Plus C) : CochainComplex.Plus C :=
  (HomotopyCategory.Plus.quotient C).objPreimage
    ((DerivedCategory.Plus.Qh (C := C)).objPreimage B)

/-- The canonical fibrant replacement used in the definition of `RHom`.

For the injective model structure on bounded-below cochain complexes, fibrant objects are
degreewise injective.  No replacement or proof certificate is supplied by the caller. -/
noncomputable def rHomInjectiveRepresentative
    [EnoughInjectives C] [HasDerivedCategory C]
    (B : DerivedCategory.Plus C) : CochainComplex.Plus C :=
  FibrantObject.HoCat.resolutionObj (rHomPlusRepresentative B)

/-- Weibel's `RHom(A,B)`: localize the total Hom complex from `A` to the chosen canonical
bounded-below fibrant representative of `B`.

Source: Weibel, Definition 10.7.2, pp. 398--401 (FC05-C10-U081).

The preceding source assertion that this computes the right derived functor, together with
choice-independence and functoriality, is not asserted here; those are Sweep-IV results. -/
noncomputable def rHom [EnoughInjectives C] [HasDerivedCategory C]
    [HasDerivedCategory AddCommGrpCat]
    (A : CochainComplex C ℤ) (B : DerivedCategory.Plus C) :
    DerivedCategory AddCommGrpCat :=
  DerivedCategory.Q.obj
    (CochainComplex.HomComplex A (rHomInjectiveRepresentative B).obj)

/-- Auxiliary caller-specified K-injective replacement data used by later comparison
constructions.  This is not the canonical owner of FC05-C10-U081; see `rHom`. -/
structure RHomInjectiveReplacement (B : CochainComplex.Plus C) where
  /-- The bounded-below replacement complex. -/
  resolution : CochainComplex.Plus C
  /-- The replacement is K-injective. -/
  [isKInjective : resolution.obj.IsKInjective]
  /-- The quasi-isomorphism from the original complex to its replacement. -/
  quasiIso : B ⟶ resolution
  /-- The displayed map is a quasi-isomorphism. -/
  [isQuasiIso : (CochainComplex.Plus.quasiIso C) quasiIso]

/-- The raw total Hom complex attached to an explicitly supplied bounded-below K-injective
replacement of `B`.

This auxiliary constructor remains useful for later comparison maps; the source-level
`RHom(A,B)` object is `rHom`. -/
def rHomViaInjectiveReplacement
    (A : CochainComplex C ℤ) (B : CochainComplex.Plus C)
    (I : RHomInjectiveReplacement B) : CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.HomComplex A I.resolution.obj

end LeanCategories.Homological
