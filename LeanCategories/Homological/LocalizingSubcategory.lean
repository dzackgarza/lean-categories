/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Localizing full subcategories

Weibel, *An Introduction to Homological Algebra* (1994), Definition 10.3.12,
pp. 379--384 (FC05-C10-U037).

For a full subcategory `B ⊂ C` and a multiplicative system `W`, Weibel calls
`B` localizing when the functor on localizations
`W_B⁻¹ B → W⁻¹ C` induced by the inclusion is fully faithful.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u

variable {C : Type u} [Category* C]

/-- Restriction of a morphism property to a full subcategory. -/
abbrev restrictedMorphismProperty
    (P : ObjectProperty C) (W : MorphismProperty C) :
    MorphismProperty P.FullSubcategory :=
  W.inverseImage P.ι

/-- The canonical functor from the localization of a full subcategory to the
localization of the ambient category. -/
noncomputable def localizedFullSubcategoryInclusion
    (P : ObjectProperty C) (W : MorphismProperty C) :
    (restrictedMorphismProperty P W).Localization ⥤ W.Localization :=
  Localization.Construction.lift (P.ι ⋙ W.Q) (by
    intro X Y f hf
    change IsIso (W.Q.map (P.ι.map f))
    exact W.Q_inverts (P.ι.map f) hf)

/-- Weibel's definition of a localizing full subcategory: localization of the
subcategory embeds fully faithfully in the ambient localization. -/
def IsLocalizingFullSubcategory
    (P : ObjectProperty C) (W : MorphismProperty C) : Prop :=
  let F := localizedFullSubcategoryInclusion P W
  F.Full ∧ F.Faithful

end LeanCategories.Homological
