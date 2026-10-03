/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import LeanCategories.Catalogue.Lift
public import LeanCategories.CategoryTheory.OneCat.KernelFunctor
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Expressions

@[expose] public section

/-!
# Kernels of formed-module morphisms (CC-LIFT)

The kernel is owned by modules: `kernel : Arr(Mod_R) → Subobjects(Mod_R)`
(`LeanCategories.kernelFunctor`, complete universal data `(K, ι)`). A morphism of formed modules
reaches it along `Arr(U) : Arr(BilinModule) → Arr(Mod_R)`, the forgetful functor `U` acting on
arrows: a derived edge (the arrow constructor is functorial), not a registered row. The result is a subobject of the *underlying module*; to be a formed submodule of the
formed module it must be lifted back, and the lift is registered data: restriction of the form
along the kernel inclusion (`BilinModuleCat.restrict`), the cartesian lift of monomorphisms along
the forgetful functor (`forgetMonoLift`). Without that row the call reports the missing lift.
-/

open CategoryTheory CategoryTheory.Limits
open LeanCategories LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration

namespace CasCatalogue

namespace CategoryId
def arrowsModules : CategoryId := ⟨"cat.arrows_modules_r"⟩
def subobjectsModules : CategoryId := ⟨"cat.subobjects_modules_r"⟩
def arrowsBilinModule : CategoryId := ⟨"cat.arrows_bilin_module"⟩
def subobjectsBilinModule : CategoryId := ⟨"cat.subobjects_bilin_module"⟩
end CategoryId

namespace FunctorId
def subobjectsBilinDomain : FunctorId := ⟨"fun.subobjects_bilin_module.domain"⟩
def subobjectsBilinInclusion : FunctorId := ⟨"fun.subobjects_bilin_module.inclusion"⟩
def arrowsModulesKernel : FunctorId := ⟨"fun.arrows_modules.kernel"⟩
end FunctorId

namespace Modules.Bilinear.Valued.Kernels

universe u

/-- Restrict the selected form to a selected submodule. This is a callable object
construction, separate from the formal cartesian-lift laws. -/
noncomputable def restricted (R : CommRingCat.{u}) (W : ModuleCat.{u} R)
    (X : BilinModuleCat R W) (N : Submodule R X.carrier) : BilinModuleCat R W :=
  X.restrict N

/-- The defining formed inclusion of the computed restriction. -/
noncomputable def restrictedInclusion (R : CommRingCat.{u}) (W : ModuleCat.{u} R)
    (X : BilinModuleCat R W) (N : Submodule R X.carrier) : restricted R W X N ⟶ X :=
  X.restrictInclusion N

/-- Compute the restricted pairing in the original selected value module. -/
noncomputable def restrictedPairing (R : CommRingCat.{u}) (W : ModuleCat.{u} R)
    (X : BilinModuleCat R W) (N : Submodule R X.carrier) :
    (N × N : Type u) ⟶ (W : Type u) :=
  TypeCat.ofHom fun xy => (restricted R W X N).pairing xy.1 xy.2

/-- Restriction preserves the actual selected form, not merely its symmetry class. -/
theorem restrictedPairing_apply (R : CommRingCat.{u}) (W : ModuleCat.{u} R)
    (X : BilinModuleCat R W) (N : Submodule R X.carrier) (x y : N) :
    restrictedPairing R W X N (x, y) = X.pairing x.val y.val := rfl

def ArrowsModules : CategoryExpr := .construct ConstructorId.arrow #[.category Modules.Modules]
def SubobjectsModules : CategoryExpr :=
  .construct ConstructorId.subobjects #[.category Modules.Modules]
def ArrowsBilin : CategoryExpr :=
  .construct ConstructorId.arrow #[.category Modules.Bilinear.Valued.Catalogue.BilinModule]
def SubobjectsBilin : CategoryExpr :=
  .construct ConstructorId.subobjects #[.category Modules.Bilinear.Valued.Catalogue.BilinModule]
def SubobjectsBilinDomainExpr : FunctorExpr SubobjectsBilin
    Modules.Bilinear.Valued.Catalogue.BilinModule := .atomic FunctorId.subobjectsBilinDomain
def SubobjectsBilinInclusionExpr : FunctorExpr SubobjectsBilin ArrowsBilin :=
  .atomic FunctorId.subobjectsBilinInclusion
def KernelExpr : FunctorExpr ArrowsModules SubobjectsModules := .atomic FunctorId.arrowsModulesKernel

noncomputable section

def arrowsModulesCategory (R : RingCat.{u}) :=
  Constructors.arrow (Modules.Mathlib.ModulesOf.{u, u} R)
def arrowsModulesRealization (R : RingCat.{u}) :
    CategoryRealization ArrowsModules (arrowsModulesCategory R) := {}
def subobjectsModulesCategory (R : RingCat.{u}) :=
  Constructors.subobjects (Modules.Mathlib.ModulesOf.{u, u} R)
def subobjectsModulesRealization (R : RingCat.{u}) :
    CategoryRealization SubobjectsModules (subobjectsModulesCategory R) := {}
def arrowsBilinCategory (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W] :=
  Constructors.arrow (bilinModuleCategory R W)
def arrowsBilinRealization (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W]
    [Module R W] : CategoryRealization ArrowsBilin (arrowsBilinCategory R W) := {}
def subobjectsBilinCategory (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W]
    [Module R W] := Constructors.subobjects (bilinModuleCategory R W)
def subobjectsBilinRealization (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W]
    [Module R W] : CategoryRealization SubobjectsBilin (subobjectsBilinCategory R W) := {}

/-- A formed subobject retains its selected restricted form on its domain. -/
def subobjectsBilinDomainDeclaration (R : Type u) [CommRing R] (W : Type u)
    [AddCommGroup W] [Module R W] :
    subobjectsBilinCategory R W ⥤ bilinModuleCategory R W :=
  (Constructors.isMonoArrow (bilinModuleCategory R W)).ι ⋙ Arrow.leftFunc

def subobjectsBilinDomainRealization (R : Type u) [CommRing R] (W : Type u)
    [AddCommGroup W] [Module R W] :
    FunctorRealization SubobjectsBilinDomainExpr (subobjectsBilinCategory R W)
      (bilinModuleCategory R W) (subobjectsBilinDomainDeclaration R W) :=
  { sourceRealization := subobjectsBilinRealization R W
    targetRealization := bilinModuleRealization R W }

/-- The actual defining inclusion of a formed subobject, with both formed endpoints. -/
def subobjectsBilinInclusionDeclaration (R : Type u) [CommRing R] (W : Type u)
    [AddCommGroup W] [Module R W] :
    subobjectsBilinCategory R W ⥤ arrowsBilinCategory R W :=
  (Constructors.isMonoArrow (bilinModuleCategory R W)).ι

def subobjectsBilinInclusionRealization (R : Type u) [CommRing R] (W : Type u)
    [AddCommGroup W] [Module R W] :
    FunctorRealization SubobjectsBilinInclusionExpr (subobjectsBilinCategory R W)
      (arrowsBilinCategory R W) (subobjectsBilinInclusionDeclaration R W) :=
  { sourceRealization := subobjectsBilinRealization R W
    targetRealization := arrowsBilinRealization R W }

/-- The kernel of a module map, with its inclusion. -/
def kernelDeclaration (R : RingCat.{u}) :
    arrowsModulesCategory R ⥤ subobjectsModulesCategory R :=
  kernelFunctor (ModuleCat.{u} R)
def kernelRealization (R : RingCat.{u}) :
    FunctorRealization KernelExpr (arrowsModulesCategory R) (subobjectsModulesCategory R)
      (kernelDeclaration R) :=
  { sourceRealization := arrowsModulesRealization R
    targetRealization := subobjectsModulesRealization R }

/-- Restriction of forms: the cartesian lift of a monomorphism `K ↪ U(X)` along the forgetful
functor `U` of formed modules is `X` restricted to the image of `K`, with its isometric
inclusion. -/
def forgetMonoLift (R : Type u) [CommRing R] (W : Type u) [AddCommGroup W] [Module R W] :
    MonoLift (forget R W) where
  obj X _ i _ := X.restrict (LinearMap.range i.hom)
  hom X _ i _ := X.restrictInclusion (LinearMap.range i.hom)
  iso X _ i hi :=
    (LinearEquiv.ofInjective i.hom ((ModuleCat.mono_iff_injective i).mp hi)).symm.toModuleIso
  fac X _ i hi := by
    ext x
    exact (LinearEquiv.ofInjective_symm_apply (f := i.hom)
      (h := (ModuleCat.mono_iff_injective i).mp hi) x).symm
  universal X K i hi Y g f hf := by
    let e := LinearEquiv.ofInjective i.hom ((ModuleCat.mono_iff_injective i).mp hi)
    have range : ∀ y, BilinModuleCat.underlyingMap f y ∈ LinearMap.range i.hom := by
      intro y
      exact ⟨g.hom y, (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hf) y).symm⟩
    let h : Y ⟶ X.restrict (LinearMap.range i.hom) :=
      BilinModuleCat.homMk ((BilinModuleCat.underlyingMap f).codRestrict _ range)
        (fun x y ↦ BilinModuleCat.map_pairing f x y)
    have hcomp : h ≫ X.restrictInclusion (LinearMap.range i.hom) = f := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      rfl
    refine ⟨h, ⟨?_, hcomp⟩, ?_⟩
    · apply (cancel_mono i).mp
      have he : e.symm.toModuleIso.hom ≫ i =
          (forget R W).map (X.restrictInclusion (LinearMap.range i.hom)) := by
        ext x
        exact LinearEquiv.ofInjective_symm_apply (f := i.hom)
          (h := (ModuleCat.mono_iff_injective i).mp hi) x
      erw [Category.assoc, he, ← Functor.map_comp, hcomp, hf]
    · intro k hk
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext y
      apply Subtype.ext
      exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
        (congrArg (forget R W).map (hk.2.trans hcomp.symm))) y

variable {R : Type u} [CommRing R] {W : Type u} [AddCommGroup W] [Module R W]

/-- The kernel of the underlying module map, as a submodule of the source. -/
def kernelSubmodule {L L' : BilinModuleCat R W} (f : L ⟶ L') : Submodule R L.carrier :=
  LinearMap.range (kernel.ι ((forget R W).map f)).hom

/-- The kernel of a formed-module morphism, as a formed module: the module kernel, lifted back
by restricting the form. -/
def formedKernel {L L' : BilinModuleCat R W} (f : L ⟶ L') : BilinModuleCat R W :=
  (forgetMonoLift R W).obj L (kernel.ι ((forget R W).map f))

/-- Its carrier is the kernel submodule. -/
theorem formedKernel_carrier {L L' : BilinModuleCat R W} (f : L ⟶ L') :
    ((formedKernel f).carrier : Type u) = kernelSubmodule f :=
  rfl

/-- Its form is the restriction of `L`'s. -/
theorem formedKernel_pairing {L L' : BilinModuleCat R W} (f : L ⟶ L')
    (x y : kernelSubmodule f) :
    (formedKernel f).pairing (show (formedKernel f).carrier from x)
      (show (formedKernel f).carrier from y) = L.pairing x.1 y.1 :=
  rfl

/-- Its elements are sent to zero by `f`. -/
theorem kernelSubmodule_map {L L' : BilinModuleCat R W} (f : L ⟶ L') (x : kernelSubmodule f) :
    BilinModuleCat.underlyingMap f x.1 = 0 := by
  obtain ⟨k, hk⟩ := x.2
  rw [← hk]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (kernel.condition ((forget R W).map f))) k

/-- The defining inclusion of the structured kernel into the selected source. -/
def formedKernelInclusion {L L' : BilinModuleCat R W} (f : L ⟶ L') :
    formedKernel f ⟶ L :=
  (forgetMonoLift R W).hom L (kernel.ι ((forget R W).map f))

/-- The defining inclusion sends a kernel element to that same source element. -/
@[simp] theorem formedKernelInclusion_apply {L L' : BilinModuleCat R W}
    (f : L ⟶ L') (x : kernelSubmodule f) :
    BilinModuleCat.underlyingMap (formedKernelInclusion f)
      (show (formedKernel f).carrier from x) = x.1 := rfl

/-- The retained inclusion is annihilated by the original underlying map. -/
theorem formedKernelInclusion_condition {L L' : BilinModuleCat R W} (f : L ⟶ L') :
    (forget R W).map (formedKernelInclusion f) ≫ (forget R W).map f = 0 := by
  ext x
  exact kernelSubmodule_map f x

end

end Modules.Bilinear.Valued.Kernels

open Modules.Bilinear.Valued.Kernels

normalized_registry .object
  { id := ⟨"obj.bilin_module.restriction"⟩, category := CategoryId.bilinModule
    name := "RestrictedForm", declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.restricted }
normalized_registry .morphism
  { id := ⟨"mor.bilin_module.restriction_inclusion"⟩, category := CategoryId.bilinModule
    name := "restriction_inclusion"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.restrictedInclusion }
normalized_registry .morphism
  { id := ⟨"mor.sets.restricted_form_pairing"⟩, category := CategoryId.sets
    name := "restricted_pairing"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.restrictedPairing }

normalized_registry .category
  { id := CategoryId.arrowsModules
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.arrowsModulesCategory
    expression := ArrowsModules
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.arrowsModulesRealization }
normalized_registry .category
  { id := CategoryId.subobjectsModules
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsModulesCategory
    expression := SubobjectsModules
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsModulesRealization }
normalized_registry .category
  { id := CategoryId.arrowsBilinModule
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.arrowsBilinCategory
    expression := ArrowsBilin
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.arrowsBilinRealization }
normalized_registry .category
  { id := CategoryId.subobjectsBilinModule
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsBilinCategory
    expression := SubobjectsBilin
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsBilinRealization }
normalized_registry .functor
  { id := FunctorId.subobjectsBilinDomain, source := SubobjectsBilin
    target := Modules.Bilinear.Valued.Catalogue.BilinModule
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsBilinDomainDeclaration
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsBilinDomainRealization
    expression := SubobjectsBilinDomainExpr, structural := true }
normalized_registry .functor
  { id := FunctorId.subobjectsBilinInclusion, source := SubobjectsBilin, target := ArrowsBilin
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsBilinInclusionDeclaration
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.subobjectsBilinInclusionRealization
    expression := SubobjectsBilinInclusionExpr }
normalized_registry .method
  { id := ⟨"meth.bilin_module.inclusion"⟩, name := "inclusion", owner := SubobjectsBilin
    functor := FunctorId.subobjectsBilinInclusion, shape := .object }

normalized_registry .functor
  { id := FunctorId.arrowsModulesKernel, source := ArrowsModules, target := SubobjectsModules
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Kernels.kernelDeclaration
    realization := `CasCatalogue.Modules.Bilinear.Valued.Kernels.kernelRealization
    expression := KernelExpr }
normalized_registry .method
  { id := ⟨"meth.kernel"⟩, name := "kernel", owner := ArrowsModules
    functor := FunctorId.arrowsModulesKernel, shape := .object, returnsToSource := true }
normalized_registry .lift
  { id := ⟨"lift.bilin_module.restrict"⟩
    edge := .constructMap ConstructorId.arrow (.functor FunctorId.bilinModuleForget)
    evidence := `CasCatalogue.Modules.Bilinear.Valued.Kernels.forgetMonoLift }

end CasCatalogue
