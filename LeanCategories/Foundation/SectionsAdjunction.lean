/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

/-!
# The constant functor is left adjoint to sections

For a category `J`, the constant functor `Δ : Sets ⥤ Fun(J, Sets)` is left adjoint to the sections
functor `F ↦ F.sections` (Mathlib `Functor.sectionsFunctor`): a natural transformation `Δ X ⟶ F`
is a cone over `F` with apex `X`, that is a map from `X` to the sections of `F`
(`Types.sectionOfCone`). By `isLimitConeOfAdj`, `sections` is therefore a limit functor on
`Fun(J, Sets)`: its value at `F` is a limit of `F`, with legs the counit (evaluation of a section)
and mediators the transposes.

Mathlib's `constLimAdj : Δ ⊣ lim` is the same adjunction up to the unique isomorphism
`lim ≅ sections` (`Types.limNatIsoSectionsFunctor`), but `lim` chooses its limits, so its
transposes do not reduce; these do.
-/

open CategoryTheory Limits

namespace LeanCategories.Foundation

universe v u w

variable (J : Type u) [Category.{v} J]

/-- `(Δ X ⟶ F) ≃ (X ⟶ sections F)`: a cone over `F` with apex `X` is a family of sections. -/
def constSectionsHomEquiv (X : Type max u w) (F : J ⥤ Type max u w) :
    ((Functor.const J).obj X ⟶ F) ≃ (X ⟶ (Functor.sectionsFunctor J).obj F) where
  toFun τ := ↾Types.sectionOfCone ⟨X, τ⟩
  invFun g :=
    { app j := ↾fun x => (g x).1 j
      naturality _ _ f := by ext x; exact ((g x).2 f).symm }
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Δ ⊣ sections`. -/
def constSectionsAdj :
    (Functor.const J : Type max u w ⥤ J ⥤ Type max u w) ⊣ Functor.sectionsFunctor J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constSectionsHomEquiv.{v, u, w} J
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

end LeanCategories.Foundation
