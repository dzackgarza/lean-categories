/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Rank
public import LeanCategories.Catalogue.Semantics.Foundation.Terminals
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Modules.Annihilator
public import LeanCategories.CategoryTheory.OneCat.ImageFunctor
public import LeanCategories.CategoryTheory.OneCat.SubobjectMap
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Catalogue
public meta import LeanCategories.Catalogue.Semantics.Modules.Rank
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels

@[expose] public section

/-!
# Operations on modules and their morphisms (`cc-dsl-migration`)

* `annihilator : Core(Mod_R) ⥤ Disc(Ideal R)` (`LeanCategories.Modules.annihilatorFunctor`), the
  iso-invariant method `annihilator` of `Mod_R`;
* `dim`: the surface name of the rank of a module (`fun.modules.rank`), for vector spaces;
* `im : Arr(Mod_R) ⥤ Subobjects(Mod_R)`, the abelian image `ker(coker(f))` with its inclusion
  into the codomain, and `ker`, the surface name of the kernel of a morphism;
* the concrete linear-map kernel as a presentation of the chosen categorical kernel,
  with both inclusions, both directions of Mathlib's canonical comparison, and naturality
  on commutative squares;
* `coim : Arr(Mod_R) ⥤ Quotients(Mod_R)`, the cokernel of its kernel inclusion, and the
  canonical comparison to `im`, with its inverse and the three defining factorization maps;
* `Sub(Mod_R) ⥤ Sub(Sets)` (`LeanCategories.subobjectMap` of the forgetful functor, a right
  adjoint and so mono-preserving): a submodule as the subset it is of the underlying set of its
  ambient module — the structural route by which a submodule reaches `contains`, `set_eq`, `⊆`;
* `Sub(Mod_R) ⥤ Mod_R`, a submodule as the module it is (the domain of its inclusion). It is
  not structural: a submodule `W ≤ V` read as the module `W` would reach `contains` as membership
  in `W` itself (always true of an element of `W`), a different operation from membership in `V`
  through the subset `W ⊆ V`. `dim` is registered on subobjects directly, as
  `rank ∘ domain : Core(Sub(Mod_R)) ⥤ Card`.
-/

open CategoryTheory
open LeanCategories CasCatalogue.Modules.Rank CasCatalogue.Modules.Bilinear.Valued.Kernels
open CasCatalogue.Foundation.Cardinality

namespace CasCatalogue

namespace CategoryId
def ideals : CategoryId := ⟨"cat.ideals_r"⟩
def coreSubobjectsModules : CategoryId := ⟨"cat.core_subobjects_modules_r"⟩
def quotientsModules : CategoryId := ⟨"cat.quotients_modules_r"⟩
end CategoryId

namespace FunctorId
def modulesAnnihilator : FunctorId := ⟨"fun.modules.annihilator"⟩
def arrowsModulesImage : FunctorId := ⟨"fun.arrows_modules.image"⟩
def subobjectsModulesForget : FunctorId := ⟨"fun.subobjects_modules.forget"⟩
def subobjectsModulesDomain : FunctorId := ⟨"fun.subobjects_modules.domain"⟩
def subobjectsModulesRank : FunctorId := ⟨"fun.subobjects_modules.rank"⟩
def subobjectsModulesInclusion : FunctorId := ⟨"fun.subobjects_modules.inclusion"⟩
def arrowsModulesCokernel : FunctorId := ⟨"fun.arrows_modules.cokernel"⟩
def quotientsModulesProjection : FunctorId := ⟨"fun.quotients_modules.projection"⟩
def quotientsModulesCodomain : FunctorId := ⟨"fun.quotients_modules.codomain"⟩
def arrowsModulesCoimage : FunctorId := ⟨"fun.arrows_modules.coimage"⟩
def arrowsModulesCoimageImageComparison : FunctorId :=
  ⟨"fun.arrows_modules.coimage_image_comparison"⟩
end FunctorId

namespace Modules.Operations

universe u

/-- The additive zero of the selected module, as a nullary operation. -/
def zero (R : RingCat.{u}) (M : ModuleCat.{u} R) :
    Foundation.Terminals.terminal.{u} ⟶
      (M : LeanCategories.Foundation.Mathlib.Sets.{u}) :=
  TypeCat.ofHom fun _ => 0

/-- Every module morphism preserves this selected additive zero. -/
theorem zero_natural (R : RingCat.{u}) (M N : ModuleCat.{u} R) (f : M ⟶ N)
    (p : PUnit.{u + 1}) :
    f.hom (ConcreteCategory.hom (C := Type u) (zero R M) p) =
      ConcreteCategory.hom (C := Type u) (zero R N) p :=
  map_zero f.hom

/-- The selected module's actual scalar action, uncurried as a map of sets.
The operands are the chosen ring and module. This operation is scoped to a common
universe; `Modules.Mathlib.ModulesOf.{u, w}` retains independent universes.

Source: `ModuleCat.smul`, `ModuleCat.smul_naturality` and
`ModuleCat.smul_restrictScalars` in Mathlib's `Algebra/Category/ModuleCat/{Basic,
ChangeOfRings}.lean`, pinned at `db584cd6d46c92f209a44c0f1c829460d327499d`
(Apache-2.0). FOUNDATIONS Definition 13.1 records the source comparison and
Formalization Corpus searches. -/
def scalarAction (R : RingCat.{u}) (M : ModuleCat.{u} R) :
    (R × M : LeanCategories.Foundation.Mathlib.Sets.{u}) ⟶
      (M : LeanCategories.Foundation.Mathlib.Sets.{u}) :=
  TypeCat.ofHom fun p => (M.smul p.1).hom p.2

/-- Evaluation of the exposed operation is the selected module's scalar action. -/
@[simp] theorem scalarAction_apply (R : RingCat.{u}) (M : ModuleCat.{u} R)
    (r : R) (m : M) :
    ConcreteCategory.hom (C := Type u) (scalarAction R M) (r, m) =
      (M.smul r).hom m := rfl

/-- Linear maps preserve the selected action, as in `ModuleCat.smul_naturality`. -/
theorem scalarAction_natural (R : RingCat.{u}) (M N : ModuleCat.{u} R)
    (f : M ⟶ N) (r : R) (m : M) :
    f.hom (ConcreteCategory.hom (C := Type u) (scalarAction R M) (r, m)) =
      ConcreteCategory.hom (C := Type u) (scalarAction R N) (r, f.hom m) :=
  (ConcreteCategory.congr_hom (ModuleCat.smul_naturality f r) m).symm

/-- Reindexing uses the chosen scalar homomorphism and the original module action. -/
theorem scalarAction_reindex {R S : RingCat.{u}} (φ : R ⟶ S)
    (N : ModuleCat.{u} S) (r : R) (n : N) :
    ConcreteCategory.hom (C := Type u)
        (scalarAction R ((LeanCategories.Modules.ModulesOverRings.reindex φ).obj N)) (r, n) =
      ConcreteCategory.hom (C := Type u) (scalarAction S N) (φ.hom r, n) :=
  ConcreteCategory.congr_hom (ModuleCat.smul_restrictScalars φ.hom r N) n

def Ideals : CategoryExpr := .atom CategoryId.ideals
def AnnihilatorExpr : FunctorExpr CoreModules Ideals := .atomic FunctorId.modulesAnnihilator
def ImageExpr : FunctorExpr ArrowsModules SubobjectsModules :=
  .atomic FunctorId.arrowsModulesImage
def SubobjectsForgetExpr : FunctorExpr SubobjectsModules Constructed.SubobjectsSets :=
  .atomic FunctorId.subobjectsModulesForget
def SubobjectsDomainExpr : FunctorExpr SubobjectsModules Modules.Modules :=
  .atomic FunctorId.subobjectsModulesDomain
def SubobjectsInclusionExpr : FunctorExpr SubobjectsModules ArrowsModules :=
  .atomic FunctorId.subobjectsModulesInclusion
def QuotientsModules : CategoryExpr := .atom CategoryId.quotientsModules
def CokernelExpr : FunctorExpr ArrowsModules QuotientsModules :=
  .atomic FunctorId.arrowsModulesCokernel
def QuotientsProjectionExpr : FunctorExpr QuotientsModules ArrowsModules :=
  .atomic FunctorId.quotientsModulesProjection
def QuotientsCodomainExpr : FunctorExpr QuotientsModules Modules.Modules :=
  .atomic FunctorId.quotientsModulesCodomain
def CoimageExpr : FunctorExpr ArrowsModules QuotientsModules :=
  .atomic FunctorId.arrowsModulesCoimage
def CoimageImageComparisonExpr : FunctorExpr ArrowsModules ArrowsModules :=
  .atomic FunctorId.arrowsModulesCoimageImageComparison
def CoreSubobjectsModules : CategoryExpr :=
  .construct ConstructorId.core #[.category SubobjectsModules]
def SubobjectsRankExpr : FunctorExpr CoreSubobjectsModules Foundation.Cardinality.Cardinals :=
  .atomic FunctorId.subobjectsModulesRank

noncomputable section

/-- The ideals of `R`, as a discrete category. -/
def idealsCategory (R : RingCat.{u}) : ObjCat.{u, u} := Cat.of (Discrete (Ideal R))
def idealsRealization (R : RingCat.{u}) : CategoryRealization Ideals (idealsCategory R) := {}

/-- `Ann_R : Core(Mod_R) ⥤ Disc(Ideal R)`. -/
def annihilatorDeclaration (R : RingCat.{u}) : coreModulesCategory R ⥤ idealsCategory R :=
  LeanCategories.Modules.annihilatorFunctor.{u, u} R
def annihilatorRealization (R : RingCat.{u}) :
    FunctorRealization AnnihilatorExpr (coreModulesCategory R) (idealsCategory R)
      (annihilatorDeclaration R) :=
  { sourceRealization := coreModulesRealization R, targetRealization := idealsRealization R }

/-- The abelian image is the kernel of the cokernel projection, retaining that inclusion.
This is `Abelian.image`, not a separately chosen image presentation. -/
def imageDeclaration (R : RingCat.{u}) :
    arrowsModulesCategory R ⥤ subobjectsModulesCategory R :=
  LeanCategories.cokernelFunctor (ModuleCat.{u} R) ⋙
    (LeanCategories.isEpiArrow (ModuleCat.{u} R)).ι ⋙
      LeanCategories.kernelFunctor (ModuleCat.{u} R)
def imageRealization (R : RingCat.{u}) :
    FunctorRealization ImageExpr (arrowsModulesCategory R) (subobjectsModulesCategory R)
      (imageDeclaration R) :=
  { sourceRealization := arrowsModulesRealization R
    targetRealization := subobjectsModulesRealization R }

/-- A submodule, as a subset of the underlying set of its ambient module. -/
def subobjectsForgetDeclaration (R : RingCat.{u}) :
    subobjectsModulesCategory R ⥤
      CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsCategory.{u} :=
  subobjectMap (C := ModuleCat.{u} R) (D := Type u) (forget (ModuleCat.{u} R))
def subobjectsForgetRealization (R : RingCat.{u}) :
    FunctorRealization SubobjectsForgetExpr (subobjectsModulesCategory R)
      CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsCategory.{u}
      (subobjectsForgetDeclaration R) :=
  { sourceRealization := subobjectsModulesRealization R
    targetRealization := CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsRealization }

/-- A submodule is the module it is: the domain of its inclusion. -/
def subobjectsDomainDeclaration (R : RingCat.{u}) :
    subobjectsModulesCategory R ⥤ Modules.Mathlib.ModulesOf.{u, u} R :=
  (Constructors.isMonoArrow (Modules.Mathlib.ModulesOf.{u, u} R)).ι ⋙ Arrow.leftFunc
def subobjectsDomainRealization (R : RingCat.{u}) :
    FunctorRealization SubobjectsDomainExpr (subobjectsModulesCategory R)
      (Modules.Mathlib.ModulesOf.{u, u} R) (subobjectsDomainDeclaration R) :=
  { sourceRealization := subobjectsModulesRealization R
    targetRealization := CasCatalogue.Modules.CatalogueRegistration.modulesRealization R }

/-- The defining inclusion, retaining its source module and ambient target. -/
def subobjectsInclusionDeclaration (R : RingCat.{u}) :
    subobjectsModulesCategory R ⥤ arrowsModulesCategory R :=
  (Constructors.isMonoArrow (Modules.Mathlib.ModulesOf.{u, u} R)).ι
def subobjectsInclusionRealization (R : RingCat.{u}) :
    FunctorRealization SubobjectsInclusionExpr (subobjectsModulesCategory R)
      (arrowsModulesCategory R) (subobjectsInclusionDeclaration R) :=
  { sourceRealization := subobjectsModulesRealization R
    targetRealization := arrowsModulesRealization R }

/-- Chosen quotient modules are epimorphisms, not merely quotient carriers. -/
def quotientsModulesCategory (R : RingCat.{u}) : ObjCat.{u + 1, u} :=
  Cat.of (LeanCategories.isEpiArrow (ModuleCat.{u} R)).FullSubcategory
def quotientsModulesRealization (R : RingCat.{u}) :
    CategoryRealization QuotientsModules (quotientsModulesCategory R) := {}

/-- The cokernel retains the actual projection from the map's codomain. -/
def cokernelDeclaration (R : RingCat.{u}) :
    arrowsModulesCategory R ⥤ quotientsModulesCategory R :=
  LeanCategories.cokernelFunctor (ModuleCat.{u} R)
def cokernelRealization (R : RingCat.{u}) :
    FunctorRealization CokernelExpr (arrowsModulesCategory R) (quotientsModulesCategory R)
      (cokernelDeclaration R) :=
  { sourceRealization := arrowsModulesRealization R
    targetRealization := quotientsModulesRealization R }

/-- A quotient's defining projection, with both module endpoints. -/
def quotientsProjectionDeclaration (R : RingCat.{u}) :
    quotientsModulesCategory R ⥤ arrowsModulesCategory R :=
  (LeanCategories.isEpiArrow (ModuleCat.{u} R)).ι
def quotientsProjectionRealization (R : RingCat.{u}) :
    FunctorRealization QuotientsProjectionExpr (quotientsModulesCategory R)
      (arrowsModulesCategory R) (quotientsProjectionDeclaration R) :=
  { sourceRealization := quotientsModulesRealization R
    targetRealization := arrowsModulesRealization R }

/-- A quotient has its selected quotient module as codomain. Structural inheritance here
is from that actual module, including its rank and underlying cardinality. -/
def quotientsCodomainDeclaration (R : RingCat.{u}) :
    quotientsModulesCategory R ⥤ Modules.Mathlib.ModulesOf.{u, u} R :=
  quotientsProjectionDeclaration R ⋙ Arrow.rightFunc
def quotientsCodomainRealization (R : RingCat.{u}) :
    FunctorRealization QuotientsCodomainExpr (quotientsModulesCategory R)
      (Modules.Mathlib.ModulesOf.{u, u} R) (quotientsCodomainDeclaration R) :=
  { sourceRealization := quotientsModulesRealization R
    targetRealization := CasCatalogue.Modules.CatalogueRegistration.modulesRealization R }

/-! The complete construction is already owned by Mathlib's abelian-category theory:
`CategoryTheory/Abelian/{Images,Basic}.lean`, at the pinned revision
`db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0).
FOUNDATIONS Definition 54.1 and corpus FC03-CE-U012 / FC05-C01-U013 specify the same
construction. The catalogue specializes it to the selected ring, with no freeness,
finite-generation or commutativity hypothesis. The formal laws below are distinct from
the callable maps published by the morphism rows. -/

/-- The coimage is the cokernel of the actual kernel inclusion, with its projection. -/
def coimageDeclaration (R : RingCat.{u}) :
    arrowsModulesCategory R ⥤ quotientsModulesCategory R :=
  kernelDeclaration R ⋙ subobjectsInclusionDeclaration R ⋙ cokernelDeclaration R

def coimageRealization (R : RingCat.{u}) :
    FunctorRealization CoimageExpr (arrowsModulesCategory R) (quotientsModulesCategory R)
      (coimageDeclaration R) :=
  { sourceRealization := arrowsModulesRealization R
    targetRealization := quotientsModulesRealization R }

/-- Mathlib's canonical coimage-to-image map, functorial on commutative squares. -/
def coimageImageComparisonDeclaration (R : RingCat.{u}) :
    arrowsModulesCategory R ⥤ arrowsModulesCategory R :=
  Abelian.coimageImageComparisonFunctor (C := ModuleCat.{u} R)

def coimageImageComparisonRealization (R : RingCat.{u}) :
    FunctorRealization CoimageImageComparisonExpr (arrowsModulesCategory R)
      (arrowsModulesCategory R) (coimageImageComparisonDeclaration R) :=
  { sourceRealization := arrowsModulesRealization R
    targetRealization := arrowsModulesRealization R }

/-- The chosen quotient module and image domain are naturally isomorphic by the
existing first-isomorphism construction in every abelian category. -/
def coimageImageIso (R : RingCat.{u}) :
    coimageDeclaration R ⋙ quotientsCodomainDeclaration R ≅
      imageDeclaration R ⋙ subobjectsDomainDeclaration R :=
  Abelian.coimIsoIm (C := ModuleCat.{u} R)

/-- The defining quotient map `M → coim(f)`. -/
def coimageProjection (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    f.left ⟶ (quotientsCodomainDeclaration R).obj ((coimageDeclaration R).obj f) :=
  Abelian.coimage.π f.hom

/-- The defining inclusion `im(f) → N`. -/
def imageInclusion (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    (subobjectsDomainDeclaration R).obj ((imageDeclaration R).obj f) ⟶ f.right :=
  Abelian.image.ι f.hom

/-- The canonical comparison, with endpoints taken from the published constructions. -/
def coimageToImage (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    (quotientsCodomainDeclaration R).obj ((coimageDeclaration R).obj f) ⟶
      (subobjectsDomainDeclaration R).obj ((imageDeclaration R).obj f) :=
  Abelian.coimageImageComparison f.hom

/-- The inverse of the same canonical comparison. -/
def imageToCoimage (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    (subobjectsDomainDeclaration R).obj ((imageDeclaration R).obj f) ⟶
      (quotientsCodomainDeclaration R).obj ((coimageDeclaration R).obj f) :=
  (Abelian.coimageIsoImage f.hom).inv

/-- The induced map from the source to the image, before its inclusion. -/
def factorThruImage (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    f.left ⟶ (subobjectsDomainDeclaration R).obj ((imageDeclaration R).obj f) :=
  Abelian.factorThruImage f.hom

/-- The induced map from the coimage to the target, after its projection. -/
def factorThruCoimage (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    (quotientsCodomainDeclaration R).obj ((coimageDeclaration R).obj f) ⟶ f.right :=
  Abelian.factorThruCoimage f.hom

/-- The three maps of the first-isomorphism factorization, composed in their defining order. -/
def coimageImageFactorization (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    f.left ⟶ f.right :=
  coimageProjection R f ≫ coimageToImage R f ≫ imageInclusion R f

/-- The factorization recovers the supplied morphism; this is Mathlib's general theorem. -/
theorem coimageImageFactorization_eq (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    coimageImageFactorization R f = f.hom :=
  Abelian.coimage_image_factorisation f.hom

/-- The projection followed by the comparison is the induced map to the image. -/
theorem coimageProjection_comp_comparison (R : RingCat.{u})
    (f : Arrow (ModuleCat.{u} R)) :
    coimageProjection R f ≫ coimageToImage R f = factorThruImage R f :=
  Limits.cokernel.π_desc _ _ _

/-- The comparison followed by the inclusion is the induced map from the coimage. -/
theorem comparison_comp_imageInclusion (R : RingCat.{u})
    (f : Arrow (ModuleCat.{u} R)) :
    coimageToImage R f ≫ imageInclusion R f = factorThruCoimage R f := by
  change Abelian.coimageImageComparison f.hom ≫ Abelian.image.ι f.hom = _
  rw [Abelian.coimageImageComparison_eq_coimageImageComparison']
  exact Limits.kernel.lift_ι _ _ _

/-- The two callable comparison maps are mutually inverse, with the chosen endpoints. -/
theorem coimageToImage_comp_imageToCoimage (R : RingCat.{u})
    (f : Arrow (ModuleCat.{u} R)) :
    coimageToImage R f ≫ imageToCoimage R f = 𝟙 _ :=
  (Abelian.coimageIsoImage f.hom).hom_inv_id

/-- The inverse identity in the image domain. -/
theorem imageToCoimage_comp_coimageToImage (R : RingCat.{u})
    (f : Arrow (ModuleCat.{u} R)) :
    imageToCoimage R f ≫ coimageToImage R f = 𝟙 _ :=
  (Abelian.coimageIsoImage f.hom).inv_hom_id

/-! ### The chosen kernel and its concrete presentation

The comparison is Mathlib's `ModuleCat.kernelIsoKer`, with its defining inclusion
equations. The concrete map on a commutative square is induced by the concrete
kernel's own universal property (`ModuleCat.kernelIsLimit` and
`KernelFork.mapOfIsLimit`), independently of the comparison. These are interface
specializations at an arbitrary ring and arrow, with no basis or dimension data.
Sources and the Formalization Corpus search record are in FOUNDATIONS Definition 54.1.
-/

/-- The concrete kernel module of the supplied linear map. -/
def linearKernel (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) : ModuleCat.{u} R :=
  ModuleCat.of R f.hom.hom.ker

/-- The actual chosen kernel subobject is the argument of its domain presentation. -/
def kernelPresentationArgument (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    subobjectsModulesCategory R :=
  (kernelDeclaration R).obj f

/-- The canonical comparison starts at the published kernel's actual domain. -/
def kernelLinearComparison (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    (subobjectsDomainDeclaration R).obj ((kernelDeclaration R).obj f) ≅ linearKernel R f :=
  ModuleCat.kernelIsoKer f.hom

/-- The defining inclusion of the actual chosen categorical kernel. -/
def kernelInclusion (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    (subobjectsDomainDeclaration R).obj ((kernelDeclaration R).obj f) ⟶ f.left :=
  ((kernelDeclaration R).obj f).obj.hom

/-- The defining inclusion of the concrete linear-map kernel. -/
def linearKernelInclusion (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    linearKernel R f ⟶ f.left :=
  ModuleCat.ofHom f.hom.hom.ker.subtype

/-- Send the chosen categorical kernel to the concrete kernel by the canonical comparison. -/
def kernelToLinearKernel (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    (subobjectsDomainDeclaration R).obj ((kernelDeclaration R).obj f) ⟶ linearKernel R f :=
  (kernelLinearComparison R f).hom

/-- The inverse comparison returns to the same chosen categorical kernel. -/
def linearKernelToKernel (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    linearKernel R f ⟶ (subobjectsDomainDeclaration R).obj ((kernelDeclaration R).obj f) :=
  (kernelLinearComparison R f).inv

/-- The forward comparison preserves the defining inclusion. -/
theorem kernelToLinearKernel_comp_inclusion (R : RingCat.{u})
    (f : Arrow (ModuleCat.{u} R)) :
    kernelToLinearKernel R f ≫ linearKernelInclusion R f = kernelInclusion R f :=
  ModuleCat.kernelIsoKer_hom_ker_subtype f.hom

/-- The inverse comparison preserves the same defining inclusion. -/
theorem linearKernelToKernel_comp_inclusion (R : RingCat.{u})
    (f : Arrow (ModuleCat.{u} R)) :
    linearKernelToKernel R f ≫ kernelInclusion R f = linearKernelInclusion R f :=
  ModuleCat.kernelIsoKer_inv_kernel_ι f.hom

/-- The two directions are inverse on the chosen categorical kernel. -/
theorem kernelToLinearKernel_comp_linearKernelToKernel (R : RingCat.{u})
    (f : Arrow (ModuleCat.{u} R)) :
    kernelToLinearKernel R f ≫ linearKernelToKernel R f = 𝟙 _ :=
  (kernelLinearComparison R f).hom_inv_id

/-- The two directions are inverse on the concrete kernel. -/
theorem linearKernelToKernel_comp_kernelToLinearKernel (R : RingCat.{u})
    (f : Arrow (ModuleCat.{u} R)) :
    linearKernelToKernel R f ≫ kernelToLinearKernel R f = 𝟙 _ :=
  (kernelLinearComparison R f).inv_hom_id

/-- A commutative square induces a map of concrete kernels by their universal property. -/
def linearKernelMap (R : RingCat.{u}) {f g : Arrow (ModuleCat.{u} R)} (s : f ⟶ g) :
    linearKernel R f ⟶ linearKernel R g :=
  (ModuleCat.kernelCone f.hom).mapOfIsLimit (ModuleCat.kernelIsLimit g.hom) s

/-- The concrete map is the restriction of the square's map on source modules. -/
@[simp] theorem linearKernelMap_apply (R : RingCat.{u})
    {f g : Arrow (ModuleCat.{u} R)} (s : f ⟶ g) (x : linearKernel R f) :
    ((linearKernelMap R s).hom x : g.hom.hom.ker).val =
      s.left.hom (x : f.hom.hom.ker).val := rfl

/-- Naturality of the concrete inclusion is the existing kernel-fork lift equation. -/
theorem linearKernelInclusion_natural (R : RingCat.{u})
    {f g : Arrow (ModuleCat.{u} R)} (s : f ⟶ g) :
    linearKernelMap R s ≫ linearKernelInclusion R g =
      linearKernelInclusion R f ≫ s.left :=
  Limits.KernelFork.mapOfIsLimit_ι _ (ModuleCat.kernelIsLimit g.hom) s

/-- The chosen kernel's inclusion is natural under the published kernel functor. -/
theorem kernelInclusion_natural (R : RingCat.{u})
    {f g : Arrow (ModuleCat.{u} R)} (s : f ⟶ g) :
    (subobjectsDomainDeclaration R).map ((kernelDeclaration R).map s) ≫ kernelInclusion R g =
      kernelInclusion R f ≫ s.left :=
  Limits.kernel.lift_ι (C := ModuleCat.{u} R) _ _ _

/-- The canonical forward comparison is natural in the actual commutative square. -/
theorem kernelToLinearKernel_natural (R : RingCat.{u})
    {f g : Arrow (ModuleCat.{u} R)} (s : f ⟶ g) :
    (subobjectsDomainDeclaration R).map ((kernelDeclaration R).map s) ≫ kernelToLinearKernel R g =
      kernelToLinearKernel R f ≫ linearKernelMap R s := by
  let k := Limits.kernel.map f.hom g.hom s.left s.right s.w.symm
  let l := (ModuleCat.kernelCone f.hom).mapOfIsLimit (ModuleCat.kernelIsLimit g.hom) s
  change k ≫ (ModuleCat.kernelIsoKer g.hom).hom = (ModuleCat.kernelIsoKer f.hom).hom ≫ l
  apply (cancel_mono (ModuleCat.ofHom g.hom.hom.ker.subtype)).1
  calc
    (k ≫ (ModuleCat.kernelIsoKer g.hom).hom) ≫ ModuleCat.ofHom g.hom.hom.ker.subtype =
        k ≫ Limits.kernel.ι g.hom :=
      (Category.assoc _ _ _).trans
        (congrArg (fun h => k ≫ h) (ModuleCat.kernelIsoKer_hom_ker_subtype g.hom))
    _ = Limits.kernel.ι f.hom ≫ s.left :=
      Limits.kernel.lift_ι (C := ModuleCat.{u} R) _ _ _
    _ = (ModuleCat.kernelIsoKer f.hom).hom ≫
        (ModuleCat.ofHom f.hom.hom.ker.subtype ≫ s.left) :=
      (congrArg (fun h => h ≫ s.left)
        (ModuleCat.kernelIsoKer_hom_ker_subtype f.hom).symm).trans (Category.assoc _ _ _)
    _ = ((ModuleCat.kernelIsoKer f.hom).hom ≫ l) ≫
        ModuleCat.ofHom g.hom.hom.ker.subtype :=
      (congrArg (fun h => (ModuleCat.kernelIsoKer f.hom).hom ≫ h)
        (Limits.KernelFork.mapOfIsLimit_ι (ModuleCat.kernelCone f.hom)
          (ModuleCat.kernelIsLimit g.hom) s).symm).trans
          (Category.assoc _ _ _).symm

/-- The inverse comparison is natural with the same chosen kernels and inclusions. -/
theorem linearKernelToKernel_natural (R : RingCat.{u})
    {f g : Arrow (ModuleCat.{u} R)} (s : f ⟶ g) :
    linearKernelMap R s ≫ linearKernelToKernel R g =
      linearKernelToKernel R f ≫
        (subobjectsDomainDeclaration R).map ((kernelDeclaration R).map s) := by
  change (ModuleCat.kernelCone f.hom).mapOfIsLimit (ModuleCat.kernelIsLimit g.hom) s ≫
      (ModuleCat.kernelIsoKer g.hom).inv =
    (ModuleCat.kernelIsoKer f.hom).inv ≫
      Limits.kernel.map f.hom g.hom s.left s.right s.w.symm
  apply (Iso.eq_inv_comp (ModuleCat.kernelIsoKer f.hom)).2
  exact (Category.assoc _ _ _).symm.trans
    ((Iso.eq_comp_inv (ModuleCat.kernelIsoKer g.hom)).2
      (kernelToLinearKernel_natural R s)).symm

/-- The public kernel domain inherits precisely the concrete kernel's cardinal rank.
This is the independence-set rank invariant over `R`, not an assumed basis cardinality. -/
theorem kernel_domain_rank (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    let K : ModuleCat.{u} R :=
      (subobjectsDomainDeclaration R).obj ((kernelDeclaration R).obj f)
    Module.rank R K = Module.rank R f.hom.hom.ker := by
  let K : ModuleCat.{u} R :=
    (subobjectsDomainDeclaration R).obj ((kernelDeclaration R).obj f)
  letI : AddCommGroup K := K.isAddCommGroup
  letI : Module R K := K.isModule
  exact LinearEquiv.rank_eq (ModuleCat.kernelIsoKer f.hom).toLinearEquiv

/-- The selected inclusion agrees with the concrete kernel inclusion under its actual
Mathlib comparison; neither the domain nor the defining map is replaced. -/
theorem kernel_inclusion (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    (ModuleCat.kernelIsoKer f.hom).inv ≫ ((kernelDeclaration R).obj f).obj.hom =
      ModuleCat.ofHom f.hom.hom.ker.subtype :=
  ModuleCat.kernelIsoKer_inv_kernel_ι f.hom

/-- The public quotient module inherits precisely the cokernel's concrete cardinal rank. -/
theorem cokernel_codomain_rank (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    let Q : ModuleCat.{u} R :=
      (quotientsCodomainDeclaration R).obj ((cokernelDeclaration R).obj f)
    Module.rank R Q = Module.rank R (f.right ⧸ f.hom.hom.range) := by
  let Q : ModuleCat.{u} R :=
    (quotientsCodomainDeclaration R).obj ((cokernelDeclaration R).obj f)
  letI : AddCommGroup Q := Q.isAddCommGroup
  letI : Module R Q := Q.isModule
  exact LinearEquiv.rank_eq (ModuleCat.cokernelIsoRangeQuotient f.hom).toLinearEquiv

/-- The retained projection is exactly the quotient projection under the actual comparison. -/
theorem cokernel_projection (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    ((cokernelDeclaration R).obj f).obj.hom ≫
        (ModuleCat.cokernelIsoRangeQuotient f.hom).hom =
      ModuleCat.ofHom f.hom.hom.range.mkQ :=
  ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom f.hom

/-- Kernel carrier cardinality is transported by the actual selected comparison. -/
theorem kernel_domain_cardinality (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    Cardinal.mk (ModuleCat.carrier (R := R)
      ((subobjectsDomainDeclaration R).obj ((kernelDeclaration R).obj f))) =
      Cardinal.mk f.hom.hom.ker :=
  Cardinal.mk_congr (ModuleCat.kernelIsoKer f.hom).toLinearEquiv.toEquiv

/-- Quotient carrier cardinality is transported by the actual selected comparison. -/
theorem cokernel_codomain_cardinality (R : RingCat.{u}) (f : Arrow (ModuleCat.{u} R)) :
    Cardinal.mk (ModuleCat.carrier (R := R)
      ((quotientsCodomainDeclaration R).obj ((cokernelDeclaration R).obj f))) =
      Cardinal.mk (f.right ⧸ f.hom.hom.range) :=
  Cardinal.mk_congr (ModuleCat.cokernelIsoRangeQuotient f.hom).toLinearEquiv.toEquiv

def coreSubobjectsModulesCategory (R : RingCat.{u}) :=
  Constructors.core (subobjectsModulesCategory R)
def coreSubobjectsModulesRealization (R : RingCat.{u}) :
    CategoryRealization CoreSubobjectsModules (coreSubobjectsModulesCategory R) := {}

/-- `dim` of a submodule: the rank of the module it is. -/
def subobjectsRankDeclaration (R : RingCat.{u}) :
    coreSubobjectsModulesCategory R ⥤ cardinalsCategory.{u} :=
  (subobjectsDomainDeclaration R).core ⋙ rankDeclaration R
def subobjectsRankRealization (R : RingCat.{u}) :
    FunctorRealization SubobjectsRankExpr (coreSubobjectsModulesCategory R) cardinalsCategory.{u}
      (subobjectsRankDeclaration R) :=
  { sourceRealization := coreSubobjectsModulesRealization R
    targetRealization := cardinalsRealization }

end

end Modules.Operations

open Modules.Operations

normalized_registry .category
  { id := CategoryId.quotientsModules, expression := QuotientsModules
    declaration := `CasCatalogue.Modules.Operations.quotientsModulesCategory
    realization := `CasCatalogue.Modules.Operations.quotientsModulesRealization }
normalized_registry .functor
  { id := FunctorId.arrowsModulesCokernel, source := ArrowsModules, target := QuotientsModules
    declaration := `CasCatalogue.Modules.Operations.cokernelDeclaration
    realization := `CasCatalogue.Modules.Operations.cokernelRealization
    expression := CokernelExpr }
normalized_registry .functor
  { id := FunctorId.quotientsModulesProjection, source := QuotientsModules, target := ArrowsModules
    declaration := `CasCatalogue.Modules.Operations.quotientsProjectionDeclaration
    realization := `CasCatalogue.Modules.Operations.quotientsProjectionRealization
    expression := QuotientsProjectionExpr }
normalized_registry .functor
  { id := FunctorId.quotientsModulesCodomain, source := QuotientsModules, target := Modules.Modules
    declaration := `CasCatalogue.Modules.Operations.quotientsCodomainDeclaration
    realization := `CasCatalogue.Modules.Operations.quotientsCodomainRealization
    expression := QuotientsCodomainExpr, structural := true }
normalized_registry .functor
  { id := FunctorId.subobjectsModulesInclusion, source := SubobjectsModules, target := ArrowsModules
    declaration := `CasCatalogue.Modules.Operations.subobjectsInclusionDeclaration
    realization := `CasCatalogue.Modules.Operations.subobjectsInclusionRealization
    expression := SubobjectsInclusionExpr }
normalized_registry .method
  { id := ⟨"meth.arrow_coker"⟩, name := "coker", owner := ArrowsModules
    functor := FunctorId.arrowsModulesCokernel, shape := .object }
normalized_registry .method
  { id := ⟨"meth.quotient_projection"⟩, name := "projection", owner := QuotientsModules
    functor := FunctorId.quotientsModulesProjection, shape := .object }
normalized_registry .method
  { id := ⟨"meth.quotient_codomain"⟩, name := "codomain", owner := QuotientsModules
    functor := FunctorId.quotientsModulesCodomain, shape := .object }
normalized_registry .method
  { id := ⟨"meth.submodule_inclusion"⟩, name := "inclusion", owner := SubobjectsModules
    functor := FunctorId.subobjectsModulesInclusion, shape := .object }

normalized_registry .category
  { id := CategoryId.ideals, declaration := `CasCatalogue.Modules.Operations.idealsCategory
    expression := Ideals, realization := `CasCatalogue.Modules.Operations.idealsRealization }
normalized_registry .functor
  { id := FunctorId.modulesAnnihilator, source := CoreModules, target := Ideals
    declaration := `CasCatalogue.Modules.Operations.annihilatorDeclaration
    realization := `CasCatalogue.Modules.Operations.annihilatorRealization
    expression := AnnihilatorExpr }
normalized_registry .functor
  { id := FunctorId.arrowsModulesImage, source := ArrowsModules, target := SubobjectsModules
    declaration := `CasCatalogue.Modules.Operations.imageDeclaration
    realization := `CasCatalogue.Modules.Operations.imageRealization
    expression := ImageExpr }
normalized_registry .functor
  { id := FunctorId.subobjectsModulesForget, source := SubobjectsModules
    target := Constructed.SubobjectsSets
    declaration := `CasCatalogue.Modules.Operations.subobjectsForgetDeclaration
    realization := `CasCatalogue.Modules.Operations.subobjectsForgetRealization
    expression := SubobjectsForgetExpr, structural := true }
normalized_registry .functor
  { id := FunctorId.subobjectsModulesDomain, source := SubobjectsModules
    target := Modules.Modules
    declaration := `CasCatalogue.Modules.Operations.subobjectsDomainDeclaration
    realization := `CasCatalogue.Modules.Operations.subobjectsDomainRealization
    expression := SubobjectsDomainExpr }
normalized_registry .method
  { id := ⟨"meth.submodule_domain"⟩, name := "domain", owner := SubobjectsModules
    functor := FunctorId.subobjectsModulesDomain, shape := .object }

normalized_registry .object
  { id := ⟨"obj.modules.linear_kernel"⟩, category := CategoryId.modulesR
    name := "linearKernel", declaration := `CasCatalogue.Modules.Operations.linearKernel
    inclusion := some `CasCatalogue.Modules.Operations.linearKernelInclusion
    functorPresentation := some
      { functor := FunctorId.subobjectsModulesDomain
        argument := `CasCatalogue.Modules.Operations.kernelPresentationArgument
        identification := `CasCatalogue.Modules.Operations.kernelLinearComparison } }

normalized_registry .category
  { id := CategoryId.coreSubobjectsModules
    declaration := `CasCatalogue.Modules.Operations.coreSubobjectsModulesCategory
    expression := CoreSubobjectsModules
    realization := `CasCatalogue.Modules.Operations.coreSubobjectsModulesRealization }
normalized_registry .functor
  { id := FunctorId.subobjectsModulesRank, source := CoreSubobjectsModules
    target := Foundation.Cardinality.Cardinals
    declaration := `CasCatalogue.Modules.Operations.subobjectsRankDeclaration
    realization := `CasCatalogue.Modules.Operations.subobjectsRankRealization
    expression := SubobjectsRankExpr }
normalized_registry .method
  { id := ⟨"meth.subobject_dim"⟩, name := "dim", owner := SubobjectsModules
    functor := FunctorId.subobjectsModulesRank, shape := .isoInvariant }
normalized_registry .method
  { id := ⟨"meth.annihilator"⟩, name := "annihilator", owner := Modules.Modules
    functor := FunctorId.modulesAnnihilator, shape := .isoInvariant }
normalized_registry .method
  { id := ⟨"meth.dim"⟩, name := "dim", owner := Modules.Modules
    functor := FunctorId.modulesRank, shape := .isoInvariant }
normalized_registry .method
  { id := ⟨"meth.arrow_ker"⟩, name := "ker", owner := ArrowsModules
    functor := FunctorId.arrowsModulesKernel, shape := .object }
normalized_registry .method
  { id := ⟨"meth.arrow_im"⟩, name := "im", owner := ArrowsModules
    functor := FunctorId.arrowsModulesImage, shape := .object }

normalized_registry .functor
  { id := FunctorId.arrowsModulesCoimage, source := ArrowsModules, target := QuotientsModules
    declaration := `CasCatalogue.Modules.Operations.coimageDeclaration
    realization := `CasCatalogue.Modules.Operations.coimageRealization
    expression := CoimageExpr }
normalized_registry .functor
  { id := FunctorId.arrowsModulesCoimageImageComparison
    source := ArrowsModules, target := ArrowsModules
    declaration := `CasCatalogue.Modules.Operations.coimageImageComparisonDeclaration
    realization := `CasCatalogue.Modules.Operations.coimageImageComparisonRealization
    expression := CoimageImageComparisonExpr }
normalized_registry .method
  { id := ⟨"meth.arrow_coim"⟩, name := "coim", owner := ArrowsModules
    functor := FunctorId.arrowsModulesCoimage, shape := .object }
normalized_registry .method
  { id := ⟨"meth.arrow_coimage_image_comparison"⟩, name := "coimageImageComparison"
    owner := ArrowsModules, functor := FunctorId.arrowsModulesCoimageImageComparison
    shape := .object }
normalized_registry .cell
  { id := ⟨"cell.modules.coimage_image"⟩, source := ArrowsModules, target := Modules.Modules
    left := #[.functor FunctorId.arrowsModulesCoimage, .functor FunctorId.quotientsModulesCodomain]
    right := #[.functor FunctorId.arrowsModulesImage, .functor FunctorId.subobjectsModulesDomain]
    declaration := `CasCatalogue.Modules.Operations.coimageImageIso, invertible := true }

normalized_registry .morphism
  { id := ⟨"mor.modules.coimage_projection"⟩, category := CategoryId.modulesR
    name := "coimageProjection", declaration := `CasCatalogue.Modules.Operations.coimageProjection }
normalized_registry .morphism
  { id := ⟨"mor.modules.image_inclusion"⟩, category := CategoryId.modulesR
    name := "imageInclusion", declaration := `CasCatalogue.Modules.Operations.imageInclusion }
normalized_registry .morphism
  { id := ⟨"mor.modules.coimage_to_image"⟩, category := CategoryId.modulesR
    name := "coimageToImage", declaration := `CasCatalogue.Modules.Operations.coimageToImage }
normalized_registry .morphism
  { id := ⟨"mor.modules.image_to_coimage"⟩, category := CategoryId.modulesR
    name := "imageToCoimage", declaration := `CasCatalogue.Modules.Operations.imageToCoimage }
normalized_registry .morphism
  { id := ⟨"mor.modules.factor_thru_image"⟩, category := CategoryId.modulesR
    name := "factorThruImage", declaration := `CasCatalogue.Modules.Operations.factorThruImage }
normalized_registry .morphism
  { id := ⟨"mor.modules.factor_thru_coimage"⟩, category := CategoryId.modulesR
    name := "factorThruCoimage", declaration := `CasCatalogue.Modules.Operations.factorThruCoimage }
normalized_registry .morphism
  { id := ⟨"mor.modules.coimage_image_factorization"⟩, category := CategoryId.modulesR
    name := "coimageImageFactorization"
    declaration := `CasCatalogue.Modules.Operations.coimageImageFactorization }

normalized_registry .morphism
  { id := ⟨"mor.modules.kernel_inclusion"⟩, category := CategoryId.modulesR
    name := "kernelInclusion", declaration := `CasCatalogue.Modules.Operations.kernelInclusion }
normalized_registry .morphism
  { id := ⟨"mor.modules.linear_kernel_inclusion"⟩, category := CategoryId.modulesR
    name := "linearKernelInclusion"
    declaration := `CasCatalogue.Modules.Operations.linearKernelInclusion }
normalized_registry .morphism
  { id := ⟨"mor.modules.kernel_to_linear_kernel"⟩, category := CategoryId.modulesR
    name := "kernelToLinearKernel"
    declaration := `CasCatalogue.Modules.Operations.kernelToLinearKernel }
normalized_registry .morphism
  { id := ⟨"mor.modules.linear_kernel_to_kernel"⟩, category := CategoryId.modulesR
    name := "linearKernelToKernel"
    declaration := `CasCatalogue.Modules.Operations.linearKernelToKernel }

normalized_registry .operation
  { id := ⟨"op.modules.zero"⟩, category := CategoryId.modulesR, name := "0", arity := 0
    declaration := `CasCatalogue.Modules.Operations.zero }

normalized_registry .operation
  { id := ⟨"op.modules.scalar_action"⟩, category := CategoryId.modulesR, name := "•", arity := 2
    declaration := `CasCatalogue.Modules.Operations.scalarAction }

end CasCatalogue
