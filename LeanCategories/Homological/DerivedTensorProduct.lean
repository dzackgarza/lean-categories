/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.TotalDerivedFunctor
public import LeanCategories.Homological.TotalTensorProduct

/-!
# Total derived tensor product

Weibel, *An Introduction to Homological Algebra* (1994), Definition 10.6.1,
pp. 394--397 (FC05-C10-U069).

For a fixed bounded-above right `R`-complex `A`, the total derived tensor
product is the total left derived functor of

`B ↦ Tot^⊕(A ⊗_R B)`.

The bounded-above decorations belong to the chosen source/derived domains;
the definition below records the localization and total-left-derived-functor
data directly.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe u uD uE

variable (R : Type u) [Ring R]

variable {D : Type uD} {E : Type uE}
  [Category* D] [Category* E]
  [Preadditive D] [Preadditive E]
  [HasZeroObject D] [HasZeroObject E]
  [HasShift D ℤ] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated D] [Pretriangulated E]

/-- Source-faithful data defining the total derived tensor product with a
fixed right complex `A`.

`qR` is the localization of left `R`-complexes, `qAb` is the localization of
complexes of abelian groups, and `derived` is the total left derived functor
of `qAb ∘ Tot^⊕(A⊗_R-)`.

Source: Weibel, Definition 10.6.1, pp. 394--397 (FC05-C10-U069). -/
structure TotalDerivedTensorProduct
    (A : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ)
    [∀ (A' : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ)
      (B : CochainComplex (ModuleCat R) ℤ),
      HomologicalComplex.HasMapBifunctor A' B (relativeTensorBifunctor R)
        (ComplexShape.up ℤ)]
    (qR : CochainComplex (ModuleCat R) ℤ ⥤ D)
    (qAb : CochainComplex (ModuleCat ℤ) ℤ ⥤ E)
    (W : MorphismProperty (CochainComplex (ModuleCat R) ℤ))
    [qR.IsLocalization W] where
  /-- The total left derived functor of the underived total tensor functor. -/
  derived : TotalLeftDerivedFunctor ((totalTensorFunctor R A) ⋙ qAb) qR W

/-- The derived tensor product `A ⊗ᴸ_R B`, evaluated on a chosen representative
`B` before localization.

Source: Weibel, Definition 10.6.1, pp. 394--397 (FC05-C10-U069). -/
def derivedTensorProduct
    (A : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ)
    [∀ (A' : CochainComplex (ModuleCat Rᵐᵒᵖ) ℤ)
      (B' : CochainComplex (ModuleCat R) ℤ),
      HomologicalComplex.HasMapBifunctor A' B' (relativeTensorBifunctor R)
        (ComplexShape.up ℤ)]
    (qR : CochainComplex (ModuleCat R) ℤ ⥤ D)
    (qAb : CochainComplex (ModuleCat ℤ) ℤ ⥤ E)
    (W : MorphismProperty (CochainComplex (ModuleCat R) ℤ))
    [qR.IsLocalization W]
    (T : TotalDerivedTensorProduct R A qR qAb W)
    (B : CochainComplex (ModuleCat R) ℤ) : E :=
  T.derived.derived.obj (qR.obj B)

end LeanCategories.Homological
