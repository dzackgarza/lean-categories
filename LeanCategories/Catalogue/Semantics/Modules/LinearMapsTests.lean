/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.LinearMaps
public import LeanCategories.Catalogue.Semantics.Modules.IntegerResidueModules
public import LeanCategories.Catalogue.Semantics.Modules.Operations
public meta import LeanCategories.Catalogue.Semantics.Modules.LinearMaps

@[expose] public section

open CategoryTheory
open CasCatalogue.Modules.CatalogueRegistration
open CasCatalogue.Modules.LinearMaps

namespace CasCatalogue.Modules.LinearMapsTests

universe u v

/-- The admission laws apply to arbitrary modules over arbitrary rings. -/
example (R : RingCat.{u}) (M : ModuleCat.{v} R) :
    IsLinearMap R (fun x : M => x + x) := by
  run_tac linearEvidence

/-- Actual morphisms retain their full linearity after forgetting to functions. -/
example (R : RingCat.{u}) (M N : ModuleCat.{v} R) (f : M ⟶ N) :
    IsLinearMap R (fun x : M => f.hom x) := by
  run_tac linearEvidence

/-- The regular-module scalar formula admits the whole nonidentity morphism. -/
theorem regular_double_linear :
    IsLinearMap (RingCat.of (ZMod 5))
      (fun x : regularModule (RingCat.of (ZMod 5)) =>
        ConcreteCategory.hom (C := Type)
          (Operations.scalarAction (RingCat.of (ZMod 5))
            (regularModule (RingCat.of (ZMod 5)))) ((2 : ZMod 5), x)) := by
  run_tac linearEvidence

/-- Admission bundles the exact familiar linear map, not merely its carrier. -/
theorem regular_double_admission :
    ConcreteCategory.hom (C := Type)
      (admitLinear (RingCat.of (ZMod 5))
        (regularModule (RingCat.of (ZMod 5))) (regularModule (RingCat.of (ZMod 5)))
        (fun x => ConcreteCategory.hom (C := Type)
          (Operations.scalarAction (RingCat.of (ZMod 5))
            (regularModule (RingCat.of (ZMod 5)))) ((2 : ZMod 5), x))
        regular_double_linear) PUnit.unit =
      ModuleCat.ofHom (X := regularModule (RingCat.of (ZMod 5)))
        (Y := regularModule (RingCat.of (ZMod 5)))
        ((2 : ZMod 5) • (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Restriction of scalars uses its actual integer action on the same residues. -/
theorem restricted_double_linear :
    IsLinearMap (RingCat.of ℤ)
      (fun x : IntegerResidueModules.integerResidueModule 5 =>
        ConcreteCategory.hom (C := Type)
          (Operations.scalarAction (RingCat.of ℤ)
            (IntegerResidueModules.integerResidueModule 5)) ((2 : ℤ), x)) := by
  run_tac linearEvidence

/-- The corresponding whole map remains the previously specified restriction. -/
theorem restricted_double_admission :
    ConcreteCategory.hom (C := Type)
      (admitLinear (RingCat.of ℤ)
        (IntegerResidueModules.integerResidueModule 5)
        (IntegerResidueModules.integerResidueModule 5)
        (fun x => ConcreteCategory.hom (C := Type)
          (Operations.scalarAction (RingCat.of ℤ)
            (IntegerResidueModules.integerResidueModule 5)) ((2 : ℤ), x))
        restricted_double_linear) PUnit.unit =
      (modulesFamilyRealization.reindex
        (RingCat.ofHom (Int.castRingHom (ZMod 5)))).map
        (ModuleCat.ofHom (X := regularModule (RingCat.of (ZMod 5)))
          (Y := regularModule (RingCat.of (ZMod 5)))
          ((2 : ZMod 5) • (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- A nearby affine function is not admitted as a linear map. -/
theorem translation_not_linear : ¬ IsLinearMap ℤ (fun x : ℤ => x + 1) := by
  intro h
  have impossible := h.map_zero
  norm_num at impossible

/-- The registered evidence does not establish the false affine admission. -/
example : True := by
  fail_if_success
    have : IsLinearMap ℤ (fun x : ℤ => x + 1) := by
      run_tac linearEvidence
  trivial

end CasCatalogue.Modules.LinearMapsTests
