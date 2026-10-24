/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Algebra.CatalogueRegistration
public import LeanCategories.Algebra.GroupKernel
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import LeanCategories.Modules.Bilinear.Valued.Cokernel
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Registered limit presentations (CC-UNIV)

* `lim.sets.pullback`: the explicit pullback of sets, `{(x, y) | f x = g y}` with its projections
  (Mathlib `Types.pullbackLimitCone`);
* `lim.sets.product`: the cartesian product `X × Y` with its projections (Mathlib
  `Types.binaryProductLimitCone`);
* `colim.sets.coproduct`: the disjoint union `X ⊕ Y` with its injections (Mathlib
  `Types.binaryCoproductColimitCocone`);
* `colim.bil_w_form.cokernel`: the cokernel of a map of formed modules with varying values, the
  quotients of the carrier and of the values by the images and the mixed relations
  (lean-categories `BilWFormCat.cokernelIsColimit`); the discriminant `L♯/L` of an integral lattice
  is the cokernel of `L → L♯`. For `A_n`, the catalogue names this cocone's apex
  `obj.bil_wform.root_lattice_a_discriminant` and its quotient leg
  `mor.bil_wform.root_lattice_a_to_discriminant`;
* `lim.groups.kernel`: the kernel `ker f ↪ G` of a group homomorphism, an equalizer of `f` and
  the trivial homomorphism (`LeanCategories.Algebra.kernelLimitCone`).

Each is a family of Mathlib `LimitCone`s: apex, legs, and the mediator `IsLimit.lift`.
-/

open CategoryTheory Limits

namespace CasCatalogue.Limits.Registration

universe u v w

/-- Set-valued diagram limits, with compatible sections, projections and universal mediator.
The construction works for arbitrary small diagram shapes, including filtered shapes; it
does not require a chosen enumeration of objects or a finite index set. -/
noncomputable def setsDiagramLimit {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) : LimitCone F :=
  ⟨Types.limitCone F, Types.limitConeIsLimit F⟩

/-- Set-valued diagram colimits, with the quotient of tagged points, injections and
universal mediator. No filteredness assumption is needed for existence. -/
noncomputable def setsDiagramColimit {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) : ColimitCocone F :=
  ⟨Types.TypeMax.colimitCocone F, Types.TypeMax.colimitCoconeIsColimit F⟩

/-- Two representatives in a filtered set colimit agree exactly when they agree after
transport to a common later object. This is stronger than mere existence of the colimit. -/
theorem setsFilteredColimit_eq_iff {J : Type v} [Category.{w} J]
    [IsFilteredOrEmpty J] (F : J ⥤ Type (max v u))
    {i j : J} (x : F.obj i) (y : F.obj j) :
    (setsDiagramColimit F).cocone.ι.app i x =
        (setsDiagramColimit F).cocone.ι.app j y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  exact Types.FilteredColimit.isColimit_eq_iff F (setsDiagramColimit F).isColimit

/-- Pullbacks in `Sets`. -/
def setsPullback {X Y Z : LeanCategories.Foundation.Mathlib.Sets.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    LimitCone (cospan f g) :=
  Types.pullbackLimitCone f g

/-- Kernels in `Grp`. -/
def groupsKernel {G H : GrpCat.{u}} (f : G ⟶ H) :
    LimitCone (parallelPair f 1) :=
  LeanCategories.Algebra.kernelLimitCone f

/-- Binary products in `Sets`. -/
def setsProduct (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) : LimitCone (pair X Y) :=
  Types.binaryProductLimitCone X Y

/-- Binary coproducts in `Sets`. -/
def setsCoproduct (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    ColimitCocone (pair X Y) :=
  Types.binaryCoproductColimitCocone X Y

/-- Cokernels of formed modules with varying values. -/
def bilWFormCokernel {R : Type u} [CommRing R]
    {X Y : LeanCategories.Modules.Bilinear.Valued.BilWFormCat R} (f : X ⟶ Y) :
    ColimitCocone (parallelPair f 0) :=
  ⟨_, LeanCategories.Modules.Bilinear.Valued.BilWFormCat.cokernelIsColimit f⟩

end CasCatalogue.Limits.Registration

namespace CasCatalogue

normalized_registry .limit
  { id := ⟨"lim.sets.diagram"⟩, category := CategoryId.sets, shape := "diagram"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramLimit }

normalized_registry .limit
  { id := ⟨"colim.sets.diagram"⟩, category := CategoryId.sets, shape := "diagram"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramColimit, colimit := true }

normalized_registry .limit
  { id := ⟨"lim.sets.pullback"⟩, category := CategoryId.sets, shape := "pullback"
    declaration := `CasCatalogue.Limits.Registration.setsPullback }

normalized_registry .limit
  { id := ⟨"lim.sets.product"⟩, category := CategoryId.sets, shape := "product"
    declaration := `CasCatalogue.Limits.Registration.setsProduct }

normalized_registry .limit
  { id := ⟨"colim.sets.coproduct"⟩, category := CategoryId.sets, shape := "coproduct"
    declaration := `CasCatalogue.Limits.Registration.setsCoproduct, colimit := true }

normalized_registry .limit
  { id := ⟨"colim.bil_w_form.cokernel"⟩, category := CategoryId.bilWForm, shape := "cokernel"
    declaration := `CasCatalogue.Limits.Registration.bilWFormCokernel, colimit := true }

normalized_registry .limit
  { id := ⟨"lim.groups.kernel"⟩, category := ⟨"cat.groups"⟩, shape := "kernel"
    declaration := `CasCatalogue.Limits.Registration.groupsKernel }

end CasCatalogue
