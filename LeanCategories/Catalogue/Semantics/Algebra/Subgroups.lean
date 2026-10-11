/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Algebra.Category.Grp.Limits
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas

@[expose] public section

/-!
# Subgroups are subobjects (CC-UNIV)

A subgroup of `G` is an object of `Subobjects(Grp)` (#54 §1): a monomorphism `H ↪ G`, so every
subgroup carries its inclusion. The generic structure is owned here, above every backend:

* `fun.subobjects_groups.domain : Subobjects(Grp) → Grp` sends a subgroup to the group it is; it is
  structural, so a subgroup inherits everything a group has (`cardinality`, `is_commutative`) with
  no declaration of its own;
* `fun.subobjects_groups.inclusion : Subobjects(Grp) → Arr(Grp)` is the full-subcategory inclusion,
  presented as the method `inclusion`: the retained universal datum, never recomputed;
* intersection and inverse image are Mathlib's `Subobject` lattice and pullback on the same
  semantic value (`GrpCat` has pullbacks); no subgroup-specific wrapper exists.

What a subgroup is, and what holds of it, is fixed here. An implementation of a subgroup
operation returns an opaque value of the declared type; any label or method inventory it attaches
is not consulted (CC-SEP, CC-PROP).
-/

open CategoryTheory
open LeanCategories LeanCategories.Algebra

namespace CasCatalogue

namespace CategoryId
def subobjectsGroups : CategoryId := ⟨"cat.subobjects_groups"⟩
def arrowsGroups : CategoryId := ⟨"cat.arrows_groups"⟩
end CategoryId

namespace FunctorId
def subobjectsGroupsDomain : FunctorId := ⟨"fun.subobjects_groups.domain"⟩
def subobjectsGroupsInclusion : FunctorId := ⟨"fun.subobjects_groups.inclusion"⟩
def arrowsGroupsKernel : FunctorId := ⟨"fun.arrows_groups.kernel"⟩
end FunctorId

namespace Algebra.Subgroups

universe u

def SubobjectsGroups : CategoryExpr :=
  .construct ConstructorId.subobjects #[.category Algebra.Catalogue.Magmas.Groups]
def ArrowsGroups : CategoryExpr :=
  .construct ConstructorId.arrow #[.category Algebra.Catalogue.Magmas.Groups]
def DomainExpr : FunctorExpr SubobjectsGroups Algebra.Catalogue.Magmas.Groups :=
  .atomic FunctorId.subobjectsGroupsDomain
def InclusionExpr : FunctorExpr SubobjectsGroups ArrowsGroups :=
  .atomic FunctorId.subobjectsGroupsInclusion
def KernelExpr : FunctorExpr ArrowsGroups SubobjectsGroups :=
  .atomic FunctorId.arrowsGroupsKernel

noncomputable section

def subobjectsGroupsCategory := Constructors.subobjects Algebra.Groups.{u}
def subobjectsGroupsRealization :
    CategoryRealization SubobjectsGroups subobjectsGroupsCategory.{u} := {}
def arrowsGroupsCategory := Constructors.arrow Algebra.Groups.{u}
def arrowsGroupsRealization : CategoryRealization ArrowsGroups arrowsGroupsCategory.{u} := {}

/-- The subgroup's chosen inclusion, with its actual ambient group retained. -/
def subgroup (G : GrpCat.{u}) (H : Subgroup G) : subobjectsGroupsCategory.{u} :=
  ⟨Arrow.mk (GrpCat.ofHom H.subtype),
    (GrpCat.mono_iff_injective _).mpr Subtype.val_injective⟩

/-- The generic kernel retains the actual homomorphism's kernel and inclusion. -/
def kernel (G H : GrpCat.{u}) (f : G ⟶ H) : subobjectsGroupsCategory.{u} :=
  subgroup G f.hom.ker

/-- A commutative square sends the selected source kernel into the selected target kernel. -/
def kernelMap {f g : Arrow GrpCat.{u}} (sq : f ⟶ g) :
    GrpCat.of f.hom.hom.ker ⟶ GrpCat.of g.hom.hom.ker :=
  GrpCat.ofHom ((sq.left.hom.comp f.hom.hom.ker.subtype).codRestrict _ (fun x => by
    change g.hom.hom (sq.left.hom x.val) = 1
    have h := ConcreteCategory.congr_hom sq.w x.val
    change g.hom.hom (sq.left.hom x.val) = sq.right.hom (f.hom.hom x.val) at h
    rw [MonoidHom.mem_ker.mp x.property, map_one] at h
    exact h))

/-- Group kernels act functorially on squares, preserving their defining inclusions. -/
def kernelDeclaration : arrowsGroupsCategory.{u} ⥤ subobjectsGroupsCategory.{u} where
  obj f := kernel f.left f.right f.hom
  map sq := ObjectProperty.homMk (Arrow.homMk (kernelMap sq) sq.left (by rfl))
  map_id f := by
    apply ObjectProperty.hom_ext
    ext x <;> rfl
  map_comp a b := by
    apply ObjectProperty.hom_ext
    ext x <;> rfl

def kernelRealization :
    FunctorRealization KernelExpr arrowsGroupsCategory.{u} subobjectsGroupsCategory.{u}
      kernelDeclaration :=
  { sourceRealization := arrowsGroupsRealization
    targetRealization := subobjectsGroupsRealization }

/-- A subgroup is the group it is: the domain of its inclusion. -/
def domainDeclaration : subobjectsGroupsCategory.{u} ⥤ Algebra.Groups.{u} :=
  (Constructors.isMonoArrow Algebra.Groups.{u}).ι ⋙ Arrow.leftFunc
def domainRealization :
    FunctorRealization DomainExpr subobjectsGroupsCategory.{u} Algebra.Groups.{u}
      domainDeclaration :=
  { sourceRealization := subobjectsGroupsRealization
    targetRealization := CasCatalogue.Algebra.CatalogueRegistration.groupsRealization }

/-- A subgroup's inclusion, as an arrow of groups. -/
def inclusionDeclaration : subobjectsGroupsCategory.{u} ⥤ arrowsGroupsCategory.{u} :=
  (Constructors.isMonoArrow Algebra.Groups.{u}).ι
def inclusionRealization :
    FunctorRealization InclusionExpr subobjectsGroupsCategory.{u} arrowsGroupsCategory.{u}
      inclusionDeclaration :=
  { sourceRealization := subobjectsGroupsRealization
    targetRealization := arrowsGroupsRealization }

end

end Algebra.Subgroups

open Algebra.Subgroups

normalized_registry .category
  { id := CategoryId.subobjectsGroups
    declaration := `CasCatalogue.Algebra.Subgroups.subobjectsGroupsCategory
    expression := SubobjectsGroups
    realization := `CasCatalogue.Algebra.Subgroups.subobjectsGroupsRealization }
normalized_registry .category
  { id := CategoryId.arrowsGroups
    declaration := `CasCatalogue.Algebra.Subgroups.arrowsGroupsCategory
    expression := ArrowsGroups
    realization := `CasCatalogue.Algebra.Subgroups.arrowsGroupsRealization }
normalized_registry .functor
  { id := FunctorId.subobjectsGroupsDomain, source := SubobjectsGroups
    target := Algebra.Catalogue.Magmas.Groups
    declaration := `CasCatalogue.Algebra.Subgroups.domainDeclaration
    realization := `CasCatalogue.Algebra.Subgroups.domainRealization
    expression := DomainExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.subobjectsGroupsInclusion, source := SubobjectsGroups, target := ArrowsGroups
    declaration := `CasCatalogue.Algebra.Subgroups.inclusionDeclaration
    realization := `CasCatalogue.Algebra.Subgroups.inclusionRealization
    expression := InclusionExpr }
normalized_registry .method
  { id := ⟨"meth.inclusion"⟩, name := "inclusion", owner := SubobjectsGroups
    functor := FunctorId.subobjectsGroupsInclusion, shape := .object }

normalized_registry .functor
  { id := FunctorId.arrowsGroupsKernel, source := ArrowsGroups, target := SubobjectsGroups
    declaration := `CasCatalogue.Algebra.Subgroups.kernelDeclaration
    realization := `CasCatalogue.Algebra.Subgroups.kernelRealization
    expression := KernelExpr }
normalized_registry .method
  { id := ⟨"meth.group_arrow_kernel"⟩, name := "ker", owner := ArrowsGroups
    functor := FunctorId.arrowsGroupsKernel, shape := .object }

end CasCatalogue
