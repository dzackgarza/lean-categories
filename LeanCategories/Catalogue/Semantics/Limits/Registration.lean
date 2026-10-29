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

/-- The selected universal mediator from a cone into the actual set-diagram limit. -/
noncomputable def setsDiagramLimitLift {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (c : Cone F) :
    c.pt ⟶ (setsDiagramLimit F).cone.pt :=
  (setsDiagramLimit F).isLimit.lift c

/-- The selected universal mediator from the actual set-diagram colimit into a cocone. -/
noncomputable def setsDiagramColimitDesc {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (c : Cocone F) :
    (setsDiagramColimit F).cocone.pt ⟶ c.pt :=
  (setsDiagramColimit F).isColimit.desc c

/-- The selected projection from a set-valued diagram limit at an arbitrary diagram object. -/
noncomputable def setsDiagramLimitProjection {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (j : J) :
    (setsDiagramLimit F).cone.pt ⟶ F.obj j :=
  (setsDiagramLimit F).cone.π.app j

/-- The selected injection into a set-valued diagram colimit at an arbitrary diagram object. -/
noncomputable def setsDiagramColimitInjection {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (j : J) :
    F.obj j ⟶ (setsDiagramColimit F).cocone.pt :=
  (setsDiagramColimit F).cocone.ι.app j

theorem setsDiagramLimitLift_fac {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (c : Cone F) (j : J) :
    setsDiagramLimitLift F c ≫ (setsDiagramLimit F).cone.π.app j = c.π.app j :=
  (setsDiagramLimit F).isLimit.fac c j

theorem setsDiagramLimitProjection_fac {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (c : Cone F) (j : J) :
    setsDiagramLimitLift F c ≫ setsDiagramLimitProjection F j = c.π.app j :=
  setsDiagramLimitLift_fac F c j

theorem setsDiagramColimitDesc_fac {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (c : Cocone F) (j : J) :
    (setsDiagramColimit F).cocone.ι.app j ≫ setsDiagramColimitDesc F c = c.ι.app j :=
  (setsDiagramColimit F).isColimit.fac c j

theorem setsDiagramColimitInjection_fac {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (c : Cocone F) (j : J) :
    setsDiagramColimitInjection F j ≫ setsDiagramColimitDesc F c = c.ι.app j :=
  setsDiagramColimitDesc_fac F c j

/-- The selected limit mediator is uniquely determined by its projection equations. -/
theorem setsDiagramLimitLift_unique {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (c : Cone F)
    (f : c.pt ⟶ (setsDiagramLimit F).cone.pt)
    (hf : ∀ j, f ≫ (setsDiagramLimit F).cone.π.app j = c.π.app j) :
    f = setsDiagramLimitLift F c :=
  (setsDiagramLimit F).isLimit.uniq c f hf

/-- The selected colimit mediator is uniquely determined by its injection equations. -/
theorem setsDiagramColimitDesc_unique {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (c : Cocone F)
    (f : (setsDiagramColimit F).cocone.pt ⟶ c.pt)
    (hf : ∀ j, (setsDiagramColimit F).cocone.ι.app j ≫ f = c.ι.app j) :
    f = setsDiagramColimitDesc F c :=
  (setsDiagramColimit F).isColimit.uniq c f hf

/-- Equality into the selected limit is detected by all its projections. -/
theorem setsDiagramLimit_hom_ext {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) {X : Type (max v u)}
    {f g : X ⟶ (setsDiagramLimit F).cone.pt}
    (h : ∀ j, f ≫ (setsDiagramLimit F).cone.π.app j =
      g ≫ (setsDiagramLimit F).cone.π.app j) : f = g :=
  (setsDiagramLimit F).isLimit.hom_ext h

/-- Equality out of the selected colimit is detected by all its injections. -/
theorem setsDiagramColimit_hom_ext {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) {X : Type (max v u)}
    {f g : (setsDiagramColimit F).cocone.pt ⟶ X}
    (h : ∀ j, (setsDiagramColimit F).cocone.ι.app j ≫ f =
      (setsDiagramColimit F).cocone.ι.app j ≫ g) : f = g :=
  (setsDiagramColimit F).isColimit.hom_ext h

/-- A natural transformation induces a morphism of the selected set-diagram limits. -/
noncomputable def setsDiagramLimitMap {J : Type v} [Category.{w} J]
    {F G : J ⥤ Type (max v u)} (α : F ⟶ G) :
    (setsDiagramLimit F).cone.pt ⟶ (setsDiagramLimit G).cone.pt :=
  (setsDiagramLimit G).isLimit.map (setsDiagramLimit F).cone α

theorem setsDiagramLimitMap_π {J : Type v} [Category.{w} J]
    {F G : J ⥤ Type (max v u)} (α : F ⟶ G) (j : J) :
    setsDiagramLimitMap α ≫ (setsDiagramLimit G).cone.π.app j =
      (setsDiagramLimit F).cone.π.app j ≫ α.app j :=
  (setsDiagramLimit G).isLimit.map_π (setsDiagramLimit F).cone α j

theorem setsDiagramLimitMap_id {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) :
    setsDiagramLimitMap (𝟙 F) = 𝟙 (setsDiagramLimit F).cone.pt := by
  apply setsDiagramLimit_hom_ext F
  intro j
  rw [setsDiagramLimitMap_π]
  simp

theorem setsDiagramLimitMap_comp {J : Type v} [Category.{w} J]
    {F G H : J ⥤ Type (max v u)} (α : F ⟶ G) (β : G ⟶ H) :
    setsDiagramLimitMap (α ≫ β) =
      setsDiagramLimitMap α ≫ setsDiagramLimitMap β := by
  apply setsDiagramLimit_hom_ext H
  intro j
  calc
    setsDiagramLimitMap (α ≫ β) ≫ (setsDiagramLimit H).cone.π.app j =
        (setsDiagramLimit F).cone.π.app j ≫ (α ≫ β).app j :=
      setsDiagramLimitMap_π (α ≫ β) j
    _ = (setsDiagramLimit F).cone.π.app j ≫ α.app j ≫ β.app j := by
      simp only [NatTrans.comp_app, Category.assoc]
    _ = (setsDiagramLimitMap α ≫ setsDiagramLimitMap β) ≫
        (setsDiagramLimit H).cone.π.app j := by
      rw [Category.assoc, setsDiagramLimitMap_π, ← Category.assoc,
        ← setsDiagramLimitMap_π, Category.assoc]

/-- A natural transformation induces a morphism of selected set-diagram colimits. -/
noncomputable def setsDiagramColimitMap {J : Type v} [Category.{w} J]
    {F G : J ⥤ Type (max v u)} (α : F ⟶ G) :
    (setsDiagramColimit F).cocone.pt ⟶ (setsDiagramColimit G).cocone.pt :=
  (setsDiagramColimit F).isColimit.map (setsDiagramColimit G).cocone α

theorem setsDiagramColimitMap_ι {J : Type v} [Category.{w} J]
    {F G : J ⥤ Type (max v u)} (α : F ⟶ G) (j : J) :
    (setsDiagramColimit F).cocone.ι.app j ≫ setsDiagramColimitMap α =
      α.app j ≫ (setsDiagramColimit G).cocone.ι.app j :=
  (setsDiagramColimit F).isColimit.ι_map (setsDiagramColimit G).cocone α j

theorem setsDiagramColimitMap_id {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) :
    setsDiagramColimitMap (𝟙 F) = 𝟙 (setsDiagramColimit F).cocone.pt := by
  apply setsDiagramColimit_hom_ext F
  intro j
  rw [setsDiagramColimitMap_ι]
  simp

theorem setsDiagramColimitMap_comp {J : Type v} [Category.{w} J]
    {F G H : J ⥤ Type (max v u)} (α : F ⟶ G) (β : G ⟶ H) :
    setsDiagramColimitMap (α ≫ β) =
      setsDiagramColimitMap α ≫ setsDiagramColimitMap β := by
  apply setsDiagramColimit_hom_ext F
  intro j
  calc
    (setsDiagramColimit F).cocone.ι.app j ≫ setsDiagramColimitMap (α ≫ β) =
        (α ≫ β).app j ≫ (setsDiagramColimit H).cocone.ι.app j :=
      setsDiagramColimitMap_ι (α ≫ β) j
    _ = α.app j ≫ β.app j ≫ (setsDiagramColimit H).cocone.ι.app j := by
      simp only [NatTrans.comp_app, Category.assoc]
    _ = (setsDiagramColimit F).cocone.ι.app j ≫
        (setsDiagramColimitMap α ≫ setsDiagramColimitMap β) := by
      rw [← setsDiagramColimitMap_ι β j, ← Category.assoc,
        ← setsDiagramColimitMap_ι α j, Category.assoc]

/-- The chosen diagram limits assemble into a functor, not just separate maps. -/
noncomputable def setsDiagramLimitFunctor {J : Type v} [Category.{w} J] :
    (J ⥤ Type (max v u)) ⥤ Type (max v u) where
  obj F := (setsDiagramLimit F).cone.pt
  map α := setsDiagramLimitMap α
  map_id F := setsDiagramLimitMap_id F
  map_comp α β := setsDiagramLimitMap_comp α β

/-- The chosen diagram colimits assemble into a functor. -/
noncomputable def setsDiagramColimitFunctor {J : Type v} [Category.{w} J] :
    (J ⥤ Type (max v u)) ⥤ Type (max v u) where
  obj F := (setsDiagramColimit F).cocone.pt
  map α := setsDiagramColimitMap α
  map_id F := setsDiagramColimitMap_id F
  map_comp α β := setsDiagramColimitMap_comp α β

/-- Two representatives in a filtered set colimit agree exactly when they agree after
transport to a common later object. This is stronger than mere existence of the colimit. -/
theorem setsFilteredColimit_eq_iff {J : Type v} [Category.{w} J]
    [IsFilteredOrEmpty J] (F : J ⥤ Type (max v u))
    {i j : J} (x : F.obj i) (y : F.obj j) :
    (setsDiagramColimit F).cocone.ι.app i x =
        (setsDiagramColimit F).cocone.ι.app j y ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  exact Types.FilteredColimit.isColimit_eq_iff F (setsDiagramColimit F).isColimit

/-- Every element of the selected set-diagram colimit has a representative at some
diagram object. This holds without a filteredness hypothesis. -/
theorem setsDiagramColimit_jointly_surjective {J : Type v} [Category.{w} J]
    (F : J ⥤ Type (max v u)) (z : (setsDiagramColimit F).cocone.pt) :
    ∃ (i : J) (x : F.obj i), (setsDiagramColimit F).cocone.ι.app i x = z := by
  exact Types.jointly_surjective F (setsDiagramColimit F).isColimit z

/-- In a filtered colimit, any two elements have representatives at a common stage. -/
theorem setsFilteredColimit_common_stage {J : Type v} [Category.{w} J]
    [IsFilteredOrEmpty J] (F : J ⥤ Type (max v u))
    (x y : (setsDiagramColimit F).cocone.pt) :
    ∃ (i : J) (x' y' : F.obj i),
      (setsDiagramColimit F).cocone.ι.app i x' = x ∧
      (setsDiagramColimit F).cocone.ι.app i y' = y := by
  exact Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (setsDiagramColimit F).isColimit x y

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
  { id := ⟨"lim.sets.diagram"⟩, category := CategoryId.sets, shape := "diagram"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramLimit }

normalized_registry .limit
  { id := ⟨"colim.sets.diagram"⟩, category := CategoryId.sets, shape := "diagram"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramColimit, colimit := true }

normalized_registry .morphism
  { id := ⟨"mor.sets.diagram_limit_lift"⟩, category := CategoryId.sets
    name := "diagram_limit_lift"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramLimitLift }

normalized_registry .morphism
  { id := ⟨"mor.sets.diagram_limit_projection"⟩, category := CategoryId.sets
    name := "diagram_limit_projection"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramLimitProjection }

normalized_registry .morphism
  { id := ⟨"mor.sets.diagram_colimit_desc"⟩, category := CategoryId.sets
    name := "diagram_colimit_desc"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramColimitDesc }

normalized_registry .morphism
  { id := ⟨"mor.sets.diagram_colimit_injection"⟩, category := CategoryId.sets
    name := "diagram_colimit_injection"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramColimitInjection }

normalized_registry .morphism
  { id := ⟨"mor.sets.diagram_limit_map"⟩, category := CategoryId.sets
    name := "diagram_limit_map"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramLimitMap }

normalized_registry .morphism
  { id := ⟨"mor.sets.diagram_colimit_map"⟩, category := CategoryId.sets
    name := "diagram_colimit_map"
    declaration := `CasCatalogue.Limits.Registration.setsDiagramColimitMap }

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
