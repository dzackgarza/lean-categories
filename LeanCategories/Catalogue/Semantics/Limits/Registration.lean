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
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
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
* `lim.modules.product`: the ordered Cartesian product of complete modules over the selected
  ring, with componentwise structure, linear projections and universal linear pairing
  (Mathlib `ModuleCat.binaryProductLimitCone`);
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

universe u v

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

/-- The ordered Cartesian product in the selected module fibre. The complete objects `M` and
`N` supply their actual additive groups and actions of the actual ring `R`. Ring and module
universes are independent. No coordinate, basis, finiteness or commutativity data is required.

This is exactly `ModuleCat.binaryProductLimitCone`, including its `LinearMap.fst`/`snd` legs,
`LinearMap.prod` mediator and full `IsLimit` proof. Source: Mathlib
`Algebra/Category/ModuleCat/Biproducts.lean` at
`db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0); the clause comparison and reuse searches
are recorded in FOUNDATIONS Definition 13.1. The chosen carrier is `M × N`; no finite-function
presentation is substituted. -/
def modulesProduct (R : RingCat.{u}) (M N : ModuleCat.{v} R) : LimitCone (pair M N) :=
  ModuleCat.binaryProductLimitCone M N

/-- Equality of the complete chosen module, including its component structures. -/
theorem modulesProduct_pt (R : RingCat.{u}) (M N : ModuleCat.{v} R) :
    (modulesProduct R M N).cone.pt = ModuleCat.of R (M × N) := rfl

/-- The product's zero is the pair of the selected component zeros. -/
theorem modulesProduct_zero (R : RingCat.{u}) (M N : ModuleCat.{v} R) :
    (0 : (modulesProduct R M N).cone.pt) = (0, 0) := rfl

/-- Addition uses the actual additive structures of both component modules. -/
theorem modulesProduct_add (R : RingCat.{u}) (M N : ModuleCat.{v} R)
    (x y : (modulesProduct R M N).cone.pt) :
    x + y = (x.1 + y.1, x.2 + y.2) := rfl

/-- Additive inverse is componentwise. -/
theorem modulesProduct_neg (R : RingCat.{u}) (M N : ModuleCat.{v} R)
    (x : (modulesProduct R M N).cone.pt) :
    -x = (-x.1, -x.2) := rfl

/-- Scalar multiplication uses both selected module actions of the same selected ring. -/
theorem modulesProduct_smul (R : RingCat.{u}) (M N : ModuleCat.{v} R) (r : R)
    (x : (modulesProduct R M N).cone.pt) :
    r • x = (r • x.1, r • x.2) := rfl

/-- The first cone leg is the ordinary linear first projection. -/
theorem modulesProduct_fst (R : RingCat.{u}) (M N : ModuleCat.{v} R) :
    (modulesProduct R M N).cone.π.app ⟨WalkingPair.left⟩ =
      ModuleCat.ofHom (LinearMap.fst R M N) :=
  ModuleCat.binaryProductLimitCone_cone_π_app_left M N

/-- The second cone leg is the ordinary linear second projection. -/
theorem modulesProduct_snd (R : RingCat.{u}) (M N : ModuleCat.{v} R) :
    (modulesProduct R M N).cone.π.app ⟨WalkingPair.right⟩ =
      ModuleCat.ofHom (LinearMap.snd R M N) :=
  ModuleCat.binaryProductLimitCone_cone_π_app_right M N

/-- The universal mediator is the linear pairing of the two supplied linear maps. -/
theorem modulesProduct_lift (R : RingCat.{u}) (M N P : ModuleCat.{v} R)
    (f : P ⟶ M) (g : P ⟶ N) :
    (modulesProduct R M N).isLimit.lift (BinaryFan.mk f g) =
      ModuleCat.ofHom (f.hom.prod g.hom) := rfl

/-- Every cone over the complete selected modules has exactly one mediating linear map.
This restates the existing `IsLimit` proof without a coordinate or finite-rank restriction. -/
theorem modulesProduct_universal (R : RingCat.{u}) (M N : ModuleCat.{v} R)
    (s : BinaryFan M N) :
    ∃! h : s.pt ⟶ (modulesProduct R M N).cone.pt,
      ∀ j, h ≫ (modulesProduct R M N).cone.π.app j = s.π.app j :=
  (modulesProduct R M N).isLimit.existsUnique s

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
  { id := ⟨"lim.sets.pullback"⟩, category := CategoryId.sets, shape := "pullback"
    declaration := `CasCatalogue.Limits.Registration.setsPullback
    standardization := some `CategoryTheory.Limits.diagramIsoCospan
    dataConstructor := some `CategoryTheory.Limits.PullbackCone.mk }

normalized_registry .limit
  { id := ⟨"lim.sets.product"⟩, category := CategoryId.sets, shape := "product"
    declaration := `CasCatalogue.Limits.Registration.setsProduct
    standardization := some `CategoryTheory.Limits.diagramIsoPair
    dataConstructor := some `CategoryTheory.Limits.BinaryFan.mk }

normalized_registry .limit
  { id := ⟨"lim.modules.product"⟩, category := CategoryId.modulesR, shape := "product"
    declaration := `CasCatalogue.Limits.Registration.modulesProduct
    standardization := some `CategoryTheory.Limits.diagramIsoPair
    dataConstructor := some `CategoryTheory.Limits.BinaryFan.mk }

normalized_registry .limit
  { id := ⟨"colim.sets.coproduct"⟩, category := CategoryId.sets, shape := "coproduct"
    declaration := `CasCatalogue.Limits.Registration.setsCoproduct, colimit := true
    standardization := some `CategoryTheory.Limits.diagramIsoPair
    dataConstructor := some `CategoryTheory.Limits.BinaryCofan.mk }

normalized_registry .limit
  { id := ⟨"colim.bil_w_form.cokernel"⟩, category := CategoryId.bilWForm, shape := "cokernel"
    declaration := `CasCatalogue.Limits.Registration.bilWFormCokernel, colimit := true
    standardization := some `CategoryTheory.Limits.diagramIsoParallelPair
    dataConstructor := some `CategoryTheory.Limits.Cofork.ofπ }

normalized_registry .limit
  { id := ⟨"lim.groups.kernel"⟩, category := ⟨"cat.groups"⟩, shape := "kernel"
    declaration := `CasCatalogue.Limits.Registration.groupsKernel
    standardization := some `CategoryTheory.Limits.diagramIsoParallelPair
    dataConstructor := some `CategoryTheory.Limits.Fork.ofι }

namespace Limits.Registration

/-- A valid diagram comparison, but in groups rather than the requested category of sets. -/
def groupPairComparison (D : Discrete WalkingPair ⥤ GrpCat.{u}) := diagramIsoPair D

/-- A valid isomorphism of the right shape that ignores the supplied diagram's objects. -/
def fixedPairComparison (_D : Discrete WalkingPair ⥤ Type) :
    pair (PUnit : Type) PUnit ≅ pair (PUnit : Type) PUnit := Iso.refl _

/-- A valid data constructor with a different complete codomain category. -/
def groupProductData {X Y P : GrpCat.{u}} (left : P ⟶ X) (right : P ⟶ Y) : BinaryFan X Y :=
  BinaryFan.mk left right

/-! Registration checks the full comparison and data schemas independently of any consumer.
The negatives use real well-typed Mathlib constructions: wrong shape, wrong category, wrong
direction, and specialization to fixed objects must all fail before a kernel can consume them. -/

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let state ← semanticState
    let some product := state.limits.find? (·.id.raw == "lim.sets.product")
      | throwError "the product presentation is not registered"
    validateLimit state product
    let rejects (description : String) (entry : LimitEntry) : MetaM Unit := do
      let accepted ← try
        validateLimit state entry
        pure true
      catch _ => pure false
      if accepted then throwError "limit validation accepted {description}"
    rejects "a cospan comparison for a product diagram" { product with
      standardization := some `CategoryTheory.Limits.diagramIsoCospan }
    rejects "a group comparison for a diagram of sets" { product with
      standardization := some `CasCatalogue.Limits.Registration.groupPairComparison }
    rejects "a fixed pair in place of the complete selected diagram" { product with
      standardization := some `CasCatalogue.Limits.Registration.fixedPairComparison }
    rejects "a cocone as product-cone data" { product with
      dataConstructor := some `CategoryTheory.Limits.BinaryCofan.mk }
    rejects "a pullback cone as product-cone data" { product with
      dataConstructor := some `CategoryTheory.Limits.PullbackCone.mk }
    rejects "group cone data for a diagram of sets" { product with
      dataConstructor := some `CasCatalogue.Limits.Registration.groupProductData }
    rejects "a universal presentation in place of plain cone data" { product with
      dataConstructor := some `CasCatalogue.Limits.Registration.setsProduct }

end Limits.Registration

end CasCatalogue
