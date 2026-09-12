/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Derived Hom representatives

Weibel, *An Introduction to Homological Algebra* (1994), Definition 10.7.2,
pp. 398--401 (FC05-C10-U081).

For a bounded-below complex `B`, a K-injective replacement `B → I` gives the standard
representative `Hom•(A,I)` for `RHom(A,B)`.  Independence of the replacement, functoriality on
the derived category, and the right-derived universal property belong to the theorem layer.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Data of a bounded-below K-injective replacement `B → I` used to compute `RHom(A,B)`. -/
structure RHomInjectiveReplacement (B : CochainComplex.Plus C) where
  /-- The bounded-below replacement complex. -/
  resolution : CochainComplex.Plus C
  /-- The replacement is K-injective. -/
  [isKInjective : resolution.obj.IsKInjective]
  /-- The quasi-isomorphism from the original complex to its replacement. -/
  quasiIso : B ⟶ resolution
  /-- The displayed map is a quasi-isomorphism. -/
  [isQuasiIso : (CochainComplex.Plus.quasiIso C) quasiIso]

/-- Weibel's `RHom(A,B)` represented using a chosen bounded-below K-injective replacement of
`B`: the total Hom complex `Hom•(A,I)`.

Source: Weibel, Definition 10.7.2, pp. 398--401 (FC05-C10-U081). -/
def rHomViaInjectiveReplacement
    (A : CochainComplex C ℤ) (B : CochainComplex.Plus C)
    (I : RHomInjectiveReplacement B) : CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.HomComplex A I.resolution.obj

end LeanCategories.Homological
