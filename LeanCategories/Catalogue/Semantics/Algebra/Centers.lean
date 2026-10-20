/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public import Mathlib.GroupTheory.Subgroup.Center
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public meta import LeanCategories.Catalogue.Semantics.Algebra.Subgroups

@[expose] public section

/-!
# Centers with their actual subgroup inclusions

Mathlib owns `Subgroup.center` and transport by `Subgroup.centerCongr`. The center is
functorial on the core of groups: an arbitrary group homomorphism need not carry the
center into the center. The target is the existing category of subgroup inclusions,
so its group structure, ambient group and defining inclusion are retained together.
-/

open CategoryTheory
namespace CasCatalogue.Algebra.Centers
universe u

/-- The center as its actual subgroup inclusion into the supplied group. -/
noncomputable def center (G : GrpCat.{u}) : Subgroups.subobjectsGroupsCategory.{u} :=
  Subgroups.subgroup G (Subgroup.center G)

/-- The retained inclusion has central image in the original group. -/
theorem center_inclusion_commutes (G : GrpCat.{u})
    (z : Subgroup.center G) (g : G) :
    g * (show G from (center G).obj.hom.hom z) =
      (show G from (center G).obj.hom.hom z) * g :=
  Subgroup.mem_center_iff.mp z.property g

/-- Isomorphisms transport centers while preserving the defining inclusions. -/
noncomputable def centers : Core GrpCat.{u} ⥤ Subgroups.subobjectsGroupsCategory.{u} where
  obj G := center G.of
  map e := ObjectProperty.homMk (Arrow.homMk
    (GrpCat.ofHom (Subgroup.centerCongr e.iso.groupIsoToMulEquiv).toMonoidHom)
    e.iso.hom (by rfl))
  map_id G := by
    apply ObjectProperty.hom_ext
    ext <;> rfl
  map_comp e f := by
    apply ObjectProperty.hom_ext
    ext <;> rfl

end CasCatalogue.Algebra.Centers

namespace CasCatalogue
namespace FunctorId
def coreGroupsCenters : FunctorId := ⟨"fun.core_groups.centers"⟩
end FunctorId

namespace Algebra.Centers
open Algebra.Automorphisms.Registration Algebra.Catalogue.Magmas

def CentersExpr : FunctorExpr CoreGroups Subgroups.SubobjectsGroups :=
  .atomic FunctorId.coreGroupsCenters

noncomputable def centersRealization :
    FunctorRealization CentersExpr coreGroupsCategory.{u}
      Subgroups.subobjectsGroupsCategory.{u} centers.{u} :=
  { sourceRealization := coreGroupsRealization
    targetRealization := Subgroups.subobjectsGroupsRealization }

end Algebra.Centers

normalized_registry .object
  { id := ⟨"obj.subgroups.center"⟩, category := CategoryId.subobjectsGroups
    name := "Center", declaration := `CasCatalogue.Algebra.Centers.center }
normalized_registry .functor
  { id := FunctorId.coreGroupsCenters
    source := Algebra.Automorphisms.Registration.CoreGroups
    target := Algebra.Subgroups.SubobjectsGroups
    declaration := `CasCatalogue.Algebra.Centers.centers
    realization := `CasCatalogue.Algebra.Centers.centersRealization
    expression := Algebra.Centers.CentersExpr }
end CasCatalogue
