/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Mathlib
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.MonCat.Adjunctions

@[expose] public section

/-!
# The total category of modules and its underlying-set functor

specs/computational-core.md CC-FIB. Modules over varying rings are the cartesian fibration
`∫ᶜ R-Mod → Ring` of restriction of scalars (FOUNDATIONS Def. 13.2), not a family of
categories. The underlying-set functor is defined once, on the total category:
`U : ∫ᶜ R-Mod ⥤ Type`, `(R, M) ↦ M`, `(φ, f) ↦ f`. "The underlying set of an `R`-module" is
`ι_R ⋙ U` (`fibreInclusion_comp_underlying`), and restriction of scalars along `φ : R ⟶ S`
does not change `U` (`underlying_obj_reindex`), because `φ^* N` has the carrier of `N`.

Searched (formalization-corpus): `CoGrothendieck forget module total`,
`forgetful functor total category of modules Grothendieck`,
`moduleCatRestrictScalarsPseudofunctor Grothendieck`. No source defines a functor out of the
total module category; the construction below is glue over Mathlib's
`Pseudofunctor.CoGrothendieck` and `RingCat.moduleCatRestrictScalarsPseudofunctor`.
-/

namespace LeanCategories.Modules

open CategoryTheory Opposite Pseudofunctor

universe u w

set_option linter.checkUnivs false

noncomputable section

/-- Modules over varying rings: the total category of the restriction-of-scalars fibration. -/
abbrev ModulesOverRings : Type _ :=
  CoGrothendieck Mathlib.moduleCatRestrictScalarsPseudofunctor.{u, w}

/-- The projection of a module to its ring: a cartesian fibration. -/
abbrev ModulesOverRings.ring : ModulesOverRings.{u, w} ⥤ RingCat.{u} :=
  CoGrothendieck.forget _

/-- The inclusion of the fibre `R-Mod` into the total category. -/
abbrev ModulesOverRings.fibreInclusion (R : RingCat.{u}) :
    ModuleCat.{w} R ⥤ ModulesOverRings.{u, w} :=
  CoGrothendieck.ι Mathlib.moduleCatRestrictScalarsPseudofunctor.{u, w} R

/-- Restriction of scalars along `φ : R ⟶ S` is the reindexing of the fibration. -/
abbrev ModulesOverRings.reindex {R S : RingCat.{u}} (φ : R ⟶ S) :
    ModuleCat.{w} S ⥤ ModuleCat.{w} R :=
  (Mathlib.moduleCatRestrictScalarsPseudofunctor.{u, w}.map φ.op.toLoc).toFunctor

/-- Reindexing is Mathlib's restriction of scalars. -/
theorem ModulesOverRings.reindex_eq {R S : RingCat.{u}} (φ : R ⟶ S) :
    ModulesOverRings.reindex.{u, w} φ = ModuleCat.restrictScalars.{w} φ.hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The underlying-set functor on the total category of modules. -/
def ModulesOverRings.underlying : ModulesOverRings.{u, w} ⥤ Type w where
  obj X := ModuleCat.carrier (R := X.base) X.fiber
  map {X Y} f := ↾fun x : ModuleCat.carrier (R := X.base) X.fiber ↦
    (f.fiber.hom x : ModuleCat.carrier (R := Y.base) Y.fiber)
  map_id X := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The supplied additive group and actual additive maps, once on the total
module fibration. A change of scalar ring does not reconstruct this group. -/
def ModulesOverRings.additiveGroup : ModulesOverRings.{u, w} ⥤ AddGrpCat.{w} where
  obj X := AddGrpCat.of (ModuleCat.carrier (R := X.base) X.fiber)
  map f := AddGrpCat.ofHom f.fiber.hom.toAddMonoidHom
  map_id X := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- Reading the supplied additive group multiplicatively and forgetting all
operations retains the existing total-module carrier and functions. -/
def ModulesOverRings.additiveGroupCarrierIso :
    ModulesOverRings.additiveGroup.{u, w} ⋙ AddGrpCat.toGrp ⋙
      forget₂ GrpCat MonCat ⋙ forget₂ MonCat Semigrp ⋙
      forget₂ Semigrp MagmaCat ⋙ forget MagmaCat ≅ ModulesOverRings.underlying.{u, w} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- On a fixed fibre the projection is the ordinary module additive-group functor. -/
theorem ModulesOverRings.fibreInclusion_comp_additiveGroup (R : RingCat.{u}) :
    ModulesOverRings.fibreInclusion.{u, w} R ⋙ ModulesOverRings.additiveGroup =
      forget₂ (ModuleCat.{w} R) AddCommGrpCat ⋙ forget₂ AddCommGrpCat AddGrpCat := rfl

/-- Restriction of scalars retains the selected additive group, including its operation. -/
theorem ModulesOverRings.additiveGroup_obj_reindex {R S : RingCat.{u}} (φ : R ⟶ S)
    (N : ModuleCat.{w} S) :
    ModulesOverRings.additiveGroup.obj
        ((ModulesOverRings.fibreInclusion R).obj ((ModulesOverRings.reindex φ).obj N)) =
      ModulesOverRings.additiveGroup.obj ((ModulesOverRings.fibreInclusion S).obj N) := rfl

/-- The underlying set of an `R`-module is the fibre inclusion followed by the one underlying-set
functor of the total category. -/
theorem ModulesOverRings.fibreInclusion_comp_underlying (R : RingCat.{u}) :
    ModulesOverRings.fibreInclusion.{u, w} R ⋙ ModulesOverRings.underlying =
      forget (ModuleCat.{w} R) :=
  rfl

/-- Restriction of scalars does not change the underlying set. -/
theorem ModulesOverRings.underlying_obj_reindex {R S : RingCat.{u}} (φ : R ⟶ S)
    (N : ModuleCat.{w} S) :
    ModulesOverRings.underlying.obj
        ((ModulesOverRings.fibreInclusion R).obj ((ModulesOverRings.reindex φ).obj N)) =
      ModulesOverRings.underlying.obj ((ModulesOverRings.fibreInclusion S).obj N) :=
  rfl

/-- The underlying map of the cartesian lift of `φ` at `N` is the identity of `N`. -/
theorem ModulesOverRings.underlying_map_cartesianLift {R S : RingCat.{u}} (φ : R ⟶ S)
    (N : ModuleCat.{w} S) :
    ModulesOverRings.underlying.map
        (CoGrothendieck.cartesianLift (F := Mathlib.moduleCatRestrictScalarsPseudofunctor.{u, w})
          N φ) = 𝟙 _ :=
  rfl

/-- The forgetful functor `Modules(R) → Sets` of the catalogue is `ι_R ⋙ U`. -/
theorem modulesToSets_eq (R : RingCat.{u}) :
    Mathlib.modulesToSets R =
      (ModulesOverRings.fibreInclusion.{u, u} R ⋙ ModulesOverRings.underlying).toCatHom :=
  rfl

/-- CC-FIB acceptance: a `ℤ/4`-module and the same group viewed as a `ℤ`-module, by restriction
along `ℤ → ℤ/4`, have one underlying set, hence one cardinality. -/
example (M : ModuleCat.{0} (RingCat.of (ZMod 4))) :
    Cardinal.mk (ModulesOverRings.underlying.obj
        ((ModulesOverRings.fibreInclusion (RingCat.of ℤ)).obj
          ((ModulesOverRings.reindex (RingCat.ofHom (Int.castRingHom (ZMod 4)))).obj M))) =
      Cardinal.mk (ModulesOverRings.underlying.obj
        ((ModulesOverRings.fibreInclusion (RingCat.of (ZMod 4))).obj M)) :=
  rfl

end

end LeanCategories.Modules
