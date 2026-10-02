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
public import LeanCategories.Modules.Bilinear.Valued.Cokernel
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Foundation.PairDiagrams
public import LeanCategories.Catalogue.Semantics.Algebra.Subgroups
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Expressions

@[expose] public section

/-!
# Registered limit presentations (CC-UNIV)

A limit row takes an object `d` of a registered category of diagrams `D` and returns a limit cone
of its diagram `F d : J ⥤ C`, whose apex is an object of the registered category `C`:

| row | input `d ∈ D` | diagram `F d` | limit |
|---|---|---|---|
| `lim.sets.pullback` | a cospan, `Fun(WalkingCospan, Sets)` | `d` | `{(x, y) | f x = g y}` |
| `lim.sets.product` | a pair, `Fun(WalkingPair, Sets)` | `d` | `X × Y` |
| `colim.sets.coproduct` | a pair, `Fun(WalkingPair, Sets)` | `d` | `X ⊕ Y` |
| `colim.bil_w_form.cokernel` | a map `f`, `Arr(BilWForm_R)` | `(f, 0)` | `coker f` |
| `lim.groups.kernel` | a homomorphism `f`, `Arr(Groups)` | `(f, 1)` | `ker f ↪ G` |

* the pullback, product and coproduct of sets are Mathlib's explicit cones
  (`Types.pullbackLimitCone`, `Types.binaryProductLimitCone`, `Types.binaryCoproductColimitCocone`)
  of the cospan or pair a diagram is isomorphic to (`diagramIsoCospan`, `diagramIsoPair`),
  transported to the diagram itself along that isomorphism; the apex is unchanged;
* the cokernel of a map of formed modules with varying values is the quotient of the carrier and of
  the values by the images and the mixed relations (lean-categories
  `BilWFormCat.cokernelIsColimit`); the discriminant `L♯/L` of an integral lattice is the cokernel
  of `L → L♯`;
* the kernel of a group homomorphism is an equalizer of `f` and the trivial homomorphism
  (`LeanCategories.Algebra.kernelLimitCone`).

A cokernel or kernel is a colimit or limit of a parallel pair one of whose maps is zero (trivial):
its input is the single map `f`, an object of the arrow category, not an arbitrary parallel pair.
-/

open CategoryTheory Limits

namespace CasCatalogue

namespace CategoryId
def walkingCospan : CategoryId := ⟨"cat.walking_cospan"⟩
def setsCospanDiagrams : CategoryId := ⟨"cat.sets.cospan_diagrams"⟩
def walkingParallelPair : CategoryId := ⟨"cat.walking_parallel_pair"⟩
def arrowsBilWForm : CategoryId := ⟨"cat.arrows_bil_wform"⟩
end CategoryId

namespace Limits.Registration

universe u

def WalkingCospanExpr : CategoryExpr := .atom CategoryId.walkingCospan
def CospanDiagramsExpr : CategoryExpr :=
  .construct ConstructorId.functorCategory #[.category WalkingCospanExpr, .category Foundation.Sets]
def WalkingParallelPairExpr : CategoryExpr := .atom CategoryId.walkingParallelPair
def ArrowsBilWFormExpr : CategoryExpr :=
  .construct ConstructorId.arrow #[.category Modules.Bilinear.Valued.Catalogue.BilWForm]

/-- The index category of cospans `· → · ← ·`. -/
def walkingCospanCategory : ObjCat.{0, 0} := Cat.of WalkingCospan
def walkingCospanRealization : CategoryRealization WalkingCospanExpr walkingCospanCategory := {}

/-- `Fun(WalkingCospan, Sets)`: the cospans of sets. -/
def cospanDiagramsCategory :=
  Constructors.functorCategory.{0, 0, u + 1, u} walkingCospanCategory
    LeanCategories.Foundation.Mathlib.Sets.{u}
def cospanDiagramsRealization :
    CategoryRealization CospanDiagramsExpr cospanDiagramsCategory.{u} := {}

/-- The index category of parallel pairs `· ⇉ ·`. -/
def walkingParallelPairCategory : ObjCat.{0, 0} := Cat.of WalkingParallelPair
def walkingParallelPairRealization :
    CategoryRealization WalkingParallelPairExpr walkingParallelPairCategory := {}

/-- `Arr(BilWForm_R)`: the maps of formed modules with varying values. -/
noncomputable def arrowsBilWFormCategory (R : Type u) [CommRing R] :=
  Constructors.arrow (Modules.Bilinear.Valued.CatalogueRegistration.bilWFormCategory R)
noncomputable def arrowsBilWFormRealization (R : Type u) [CommRing R] :
    CategoryRealization ArrowsBilWFormExpr (arrowsBilWFormCategory R) := {}

/-- Pullbacks in `Sets`: the limit of a cospan `F` is `{(x, y) | F.map inl x = F.map inr y}`. -/
def setsPullback (F : WalkingCospan ⥤ LeanCategories.Foundation.Mathlib.Sets.{u}) :
    LimitCone F :=
  let c := Types.pullbackLimitCone (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr)
  ⟨(Cones.postcompose (diagramIsoCospan F).inv).obj c.cone,
    (IsLimit.postcomposeInvEquiv (diagramIsoCospan F) c.cone).symm c.isLimit⟩

/-- Binary products in `Sets`: the limit of a pair `F` is `F left × F right`. -/
def setsProduct (F : Discrete WalkingPair ⥤ LeanCategories.Foundation.Mathlib.Sets.{u}) :
    LimitCone F :=
  let c := Types.binaryProductLimitCone (F.obj ⟨.left⟩) (F.obj ⟨.right⟩)
  ⟨(Cones.postcompose (diagramIsoPair F).inv).obj c.cone,
    (IsLimit.postcomposeInvEquiv (diagramIsoPair F) c.cone).symm c.isLimit⟩

/-- Binary coproducts in `Sets`: the colimit of a pair `F` is `F left ⊕ F right`. -/
def setsCoproduct (F : Discrete WalkingPair ⥤ LeanCategories.Foundation.Mathlib.Sets.{u}) :
    ColimitCocone F :=
  let c := Types.binaryCoproductColimitCocone (F.obj ⟨.left⟩) (F.obj ⟨.right⟩)
  ⟨(Cocones.precompose (diagramIsoPair F).hom).obj c.cocone,
    (IsColimit.precomposeHomEquiv (diagramIsoPair F) c.cocone).symm c.isColimit⟩

/-- Kernels in `Grp`: the limit of the parallel pair `(f, 1)` of a homomorphism `f`. -/
def groupsKernel (f : Arrow GrpCat.{u}) : LimitCone (parallelPair f.hom 1) :=
  LeanCategories.Algebra.kernelLimitCone f.hom

/-- Cokernels of formed modules with varying values: the colimit of the parallel pair `(f, 0)`
of a map `f`. -/
def bilWFormCokernel {R : Type u} [CommRing R]
    (f : Arrow (LeanCategories.Modules.Bilinear.Valued.BilWFormCat R)) :
    ColimitCocone (parallelPair f.hom 0) :=
  ⟨_, LeanCategories.Modules.Bilinear.Valued.BilWFormCat.cokernelIsColimit f.hom⟩

end Limits.Registration

open Limits.Registration

normalized_registry .category
  { id := CategoryId.walkingCospan
    declaration := `CasCatalogue.Limits.Registration.walkingCospanCategory
    expression := WalkingCospanExpr
    realization := `CasCatalogue.Limits.Registration.walkingCospanRealization }

normalized_registry .category
  { id := CategoryId.setsCospanDiagrams
    declaration := `CasCatalogue.Limits.Registration.cospanDiagramsCategory
    expression := CospanDiagramsExpr
    realization := `CasCatalogue.Limits.Registration.cospanDiagramsRealization }

normalized_registry .category
  { id := CategoryId.walkingParallelPair
    declaration := `CasCatalogue.Limits.Registration.walkingParallelPairCategory
    expression := WalkingParallelPairExpr
    realization := `CasCatalogue.Limits.Registration.walkingParallelPairRealization }

normalized_registry .category
  { id := CategoryId.arrowsBilWForm
    declaration := `CasCatalogue.Limits.Registration.arrowsBilWFormCategory
    expression := ArrowsBilWFormExpr
    realization := `CasCatalogue.Limits.Registration.arrowsBilWFormRealization }

normalized_registry .limit
  { id := ⟨"lim.sets.pullback"⟩, category := CategoryId.sets, shape := CategoryId.walkingCospan
    diagrams := CategoryId.setsCospanDiagrams
    declaration := `CasCatalogue.Limits.Registration.setsPullback }

normalized_registry .limit
  { id := ⟨"lim.sets.product"⟩, category := CategoryId.sets, shape := CategoryId.walkingPair
    diagrams := CategoryId.setsPairDiagrams
    declaration := `CasCatalogue.Limits.Registration.setsProduct }

normalized_registry .limit
  { id := ⟨"colim.sets.coproduct"⟩, category := CategoryId.sets, shape := CategoryId.walkingPair
    diagrams := CategoryId.setsPairDiagrams
    declaration := `CasCatalogue.Limits.Registration.setsCoproduct, colimit := true }

normalized_registry .limit
  { id := ⟨"colim.bil_w_form.cokernel"⟩, category := CategoryId.bilWForm
    shape := CategoryId.walkingParallelPair, diagrams := CategoryId.arrowsBilWForm
    declaration := `CasCatalogue.Limits.Registration.bilWFormCokernel, colimit := true }

normalized_registry .limit
  { id := ⟨"lim.groups.kernel"⟩, category := CategoryId.groups
    shape := CategoryId.walkingParallelPair, diagrams := CategoryId.arrowsGroups
    declaration := `CasCatalogue.Limits.Registration.groupsKernel }

end CasCatalogue
