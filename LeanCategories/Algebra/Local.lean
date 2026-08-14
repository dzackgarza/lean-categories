/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Local algebra routes

Mathlib owns localization of rings and modules, localization at prime ideals,
fraction rings, local rings, residue fields, and adic completions. This module
exposes the canonical definitions and functorial maps directly.
-/

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.LocalRing

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u

/-- The residue field of a commutative local ring, using Mathlib's canonical quotient.

The local-ring hypothesis is carried by the object of `LocalRingCat`. -/
noncomputable def residueField (R : LocalRingCat.{u}) : CommRingCat.{u} :=
  letI : IsLocalRing (R.1 : Type u) := R.2
  CommRingCat.of (IsLocalRing.ResidueField R.1)

/-- The canonical quotient map from a local ring to its residue field. -/
noncomputable def residue (R : LocalRingCat.{u}) :
    (R.1 : Type u) →+* (residueField R : Type u) :=
  letI : IsLocalRing (R.1 : Type u) := R.2
  IsLocalRing.residue R.1

/- The residue-field map is functorial on the category of local homomorphisms.

This uses Mathlib's `IsLocalRing.ResidueField.map`, `map_id`, and `map_comp`.
-/
noncomputable def residueFieldHomFunctor :
    LocalRingHomCat.{u} ⥤ CategoryTheory.Arrow CommRingCat.{u} where
  obj f := CategoryTheory.Arrow.mk
    (CommRingCat.ofHom (IsLocalRing.ResidueField.map f.hom.hom))
  map g := CategoryTheory.Arrow.homMk
    (CommRingCat.ofHom (IsLocalRing.ResidueField.map g.left.hom))
    (CommRingCat.ofHom (IsLocalRing.ResidueField.map g.right.hom)) (by
      apply CommRingCat.hom_ext
      ext x
      simpa only [CategoryTheory.Arrow.comp_right, CategoryTheory.Arrow.comp_left,
        CategoryTheory.CategoryStruct.comp, CommRingCat.comp_ofHom,
        IsLocalRing.ResidueField.map_comp] using congrArg DFunLike.coe g.w)
  map_id f := by
    apply CategoryTheory.Arrow.Hom.ext <;> simp
  map_comp f g := by
    apply CategoryTheory.Arrow.Hom.ext <;> simp [CategoryTheory.Arrow.comp_right,
      CategoryTheory.Arrow.comp_left]

end LeanCategories.Algebra
