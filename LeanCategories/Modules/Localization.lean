/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Localization of modules

Mathlib provides localization of an `R`-module at a submonoid `S` as
`ModuleCat.localizedModule`. This file exposes that object and its canonical
map under the project module namespace.
-/

public import Mathlib.Algebra.Category.ModuleCat.Localization

@[expose] public section

namespace LeanCategories.Modules

universe u v

variable {R : Type u} [CommRing R]

/** A module of fractions, using Mathlib's canonical localized module. */
noncomputable abbrev moduleOfFractions [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : ModuleCat.{v} (Localization S) :=
  ModuleCat.localizedModule M S

/** The canonical map from a module to its module of fractions. */
noncomputable abbrev moduleOfFractionsMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M →ₗ[R] moduleOfFractions M S :=
  ModuleCat.localizedModuleMkLinearMap M S

/** The canonical morphism between modules of fractions. */
noncomputable abbrev moduleOfFractionsHom [Small.{v} R]
    {M N : ModuleCat.{v} R} (S : Submonoid R) (f : M ⟶ N) :
    moduleOfFractions M S ⟶ moduleOfFractions N S :=
  ModuleCat.localizedModuleMap S f

/** Localization of modules as Mathlib's canonical functor. */
noncomputable abbrev moduleOfFractionsFunctor [Small.{v} R] (S : Submonoid R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S) :=
  ModuleCat.localizedModuleFunctor S

/-- The `ModuleCat (Localization S)` object obtained by localizing `M` at `S`. -/
noncomputable abbrev localizedModule [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : ModuleCat.{v} (Localization S) :=
  ModuleCat.localizedModule M S

/-- The canonical `R`-linear map from `M` to its localization. -/
noncomputable abbrev localizedModuleMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M →ₗ[R] localizedModule M S :=
  ModuleCat.localizedModuleMkLinearMap M S

/-- The canonical morphism between localized module objects. -/
noncomputable abbrev localizedModuleHom [Small.{v} R]
    {M N : ModuleCat.{v} R} (S : Submonoid R) (f : M ⟶ N) :
    localizedModule M S ⟶ localizedModule N S :=
  ModuleCat.localizedModuleMap S f

/-- Localization as Mathlib's canonical functor between module categories. -/
noncomputable abbrev localizedModuleFunctor [Small.{v} R] (S : Submonoid R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S) :=
  ModuleCat.localizedModuleFunctor S

end LeanCategories.Modules
