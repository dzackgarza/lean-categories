/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.LocalizingSubcategory
public import Mathlib.CategoryTheory.Equivalence

/-!
# Localizing domains for total derived functors

Weibel, *An Introduction to Homological Algebra* (1994), §10.5,
pp. 390--393 (FC05-C10-U054).

Before defining total derived functors, Weibel fixes a localizing triangulated
subcategory `K` of the homotopy category and denotes by `D` the corresponding
full subcategory of the derived category.  The structure below records exactly
that convention for an arbitrary localization functor.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe u v

variable {C : Type u} {D : Type v} [Category* C] [Category* D]

/-- A chosen localizing homotopy-domain together with the corresponding full
subcategory of the localized/derived category.

The restricted localization functor is required to be an equivalence onto the
chosen derived-domain.  This is the data behind Weibel's conventions such as
`K⁺(A)` paired with `D⁺(A)`.

Source: Weibel, §10.5, pp. 390--393 (FC05-C10-U054). -/
structure DerivedDomainConvention
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W] where
  /-- The chosen localizing subcategory of the homotopy category. -/
  homotopyDomain : ObjectProperty C
  /-- The corresponding full subcategory of the derived category. -/
  derivedDomain : ObjectProperty D
  /-- The source domain is localizing for the chosen weak equivalences. -/
  localizing : IsLocalizingFullSubcategory homotopyDomain W
  /-- Restriction of the localization functor to the paired full subcategories. -/
  restricted : homotopyDomain.FullSubcategory ⥤ derivedDomain.FullSubcategory
  /-- Forgetting the full-subcategory wrappers recovers the ambient localization. -/
  restricted_comp : restricted ⋙ derivedDomain.ι = homotopyDomain.ι ⋙ Q
  /-- The restricted localization is full. -/
  [restrictedFull : restricted.Full]
  /-- The restricted localization is faithful. -/
  [restrictedFaithful : restricted.Faithful]
  /-- Every object of the chosen derived-domain comes from the homotopy-domain. -/
  [restrictedEssSurj : restricted.EssSurj]

end LeanCategories.Homological
