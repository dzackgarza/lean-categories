/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Types.Products
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue

@[expose] public section

/-!
# The ordered Cartesian product of sets

This interface publishes Mathlib's explicit `Types.binaryProductFunctor`, whose object is
`X × Y`, together with its actual projections, pairing, map and isomorphism action. Its source
and target are the already registered `Sets` and `Fun(Sets, Sets)`. The two declared object
components retain their order. `componentIsLimit` publishes the full universal cone of these
exact coordinates, including its mediator. Every set and map is a parameter; no enumeration
or finiteness is required.

The complete universal cone is already registered as `lim.sets.product`, from
`Types.binaryProductLimitCone`. `coneComparison` compares this explicit product with any
supplied full limit cone, retaining that cone's own legs. `chosenComparison` is Mathlib's
`Types.binaryProductIsoProd`, with its full naturality. Neither comparison identifies an
arbitrary cone apex or its projections by carrier equality.

Sources: Mathlib `CategoryTheory/Limits/Types/Products.lean`, `Limits/IsLimit.lean`,
`Functor/Currying.lean`, and `Products/Basic.lean` at
`db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0), inspected before this interface.
FOUNDATIONS Definition 4.4 records the mathematical statement and reuse searches. The lemmas
below expose those existing constructions; they are interface equations, not new product theory.
-/

open CategoryTheory Limits
open scoped CategoryTheory.Prod

namespace CasCatalogue

namespace FunctorId
def setsOrderedProduct : FunctorId := ⟨"fun.sets.ordered_product"⟩
end FunctorId

namespace Foundation.OrderedProducts

universe u

def ProductExpr : FunctorExpr Foundation.Sets Constructed.EndofunctorsSets :=
  .atomic FunctorId.setsOrderedProduct

/-- The complete ordered product bifunctor, in Mathlib's curried presentation. -/
def productDeclaration : LeanCategories.Foundation.Mathlib.Sets.{u} ⥤
    Catalogue.ConstructorRegistration.endofunctorsSetsCategory.{u} :=
  Types.binaryProductFunctor

noncomputable def productRealization :
    FunctorRealization ProductExpr LeanCategories.Foundation.Mathlib.Sets.{u}
      Catalogue.ConstructorRegistration.endofunctorsSetsCategory.{u} productDeclaration :=
  { sourceRealization := Foundation.CatalogueRegistration.setsRealization
    targetRealization := Catalogue.ConstructorRegistration.endofunctorsSetsRealization }

/-- The literal ordered object `X × Y`, as the value of the published bifunctor. -/
def product (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    LeanCategories.Foundation.Mathlib.Sets.{u} :=
  (productDeclaration.obj X).obj Y

/-- The first projection of the existing explicit product cone. -/
def fst (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) : product X Y ⟶ X :=
  (Types.binaryProductCone X Y).fst

/-- The second projection of the existing explicit product cone. -/
def snd (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) : product X Y ⟶ Y :=
  (Types.binaryProductCone X Y).snd

/-- The ordered object has exactly two declared components. -/
def arity (_X _Y : LeanCategories.Foundation.Mathlib.Sets.{u}) : ℕ := 2

/-- Component zero is `X`; component one is `Y`. -/
def component (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    Fin 2 → LeanCategories.Foundation.Mathlib.Sets.{u} :=
  Fin.cases X fun _ => Y

/-- The finite component metadata uses the actual ordered cone projections. -/
def projection (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) (i : Fin (arity X Y)) :
    product X Y ⟶ component X Y i :=
  Fin.cases (fst X Y) (fun _ => snd X Y) i

/-- Pair two maps at their original arbitrary stage, using the existing universal mediator. -/
def pairing (T X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) (f : T ⟶ X) (g : T ⟶ Y) :
    T ⟶ product X Y :=
  BinaryFan.IsLimit.lift (Types.binaryProductLimit X Y) f g

/-- The two-variable map action of the published functor, retaining both supplied maps. -/
def map (X X' Y Y' : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : X ⟶ X') (g : Y ⟶ Y') : product X Y ⟶ product X' Y' :=
  (Functor.uncurry.obj productDeclaration).map (f ×ₘ g)

/-- Componentwise transport, with both actual isomorphisms and their inverse maps. -/
def iso (X X' Y Y' : LeanCategories.Foundation.Mathlib.Sets.{u})
    (e : X ≅ X') (d : Y ≅ Y') : product X Y ≅ product X' Y' :=
  (Functor.uncurry.obj productDeclaration).mapIso (e.prod d)

/-- The actual comparison to any supplied full limit cone on the same ordered pair. -/
def coneComparison (X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (s : LimitCone (Limits.pair X Y)) : product X Y ≅ s.cone.pt :=
  (Types.binaryProductLimit X Y).conePointUniqueUpToIso s.isLimit

/-- Mathlib's natural comparison with its chosen categorical product functor. -/
noncomputable def chosenComparison :
    productDeclaration.{u} ≅ (Limits.prod.functor : Type u ⥤ Type u ⥤ Type u) :=
  Types.binaryProductIsoProd

theorem product_eq (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    product X Y = (X × Y) := rfl

theorem projection_zero (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    projection X Y (0 : Fin 2) = fst X Y := rfl

theorem projection_one (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    projection X Y (1 : Fin 2) = snd X Y := rfl

theorem pairing_apply (T X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : T ⟶ X) (g : T ⟶ Y) (t : T) : pairing T X Y f g t = (f t, g t) := rfl

theorem pairing_fst (T X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : T ⟶ X) (g : T ⟶ Y) : pairing T X Y f g ≫ fst X Y = f :=
  BinaryFan.IsLimit.lift_fst (Types.binaryProductLimit X Y) f g

theorem pairing_snd (T X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : T ⟶ X) (g : T ⟶ Y) : pairing T X Y f g ≫ snd X Y = g :=
  BinaryFan.IsLimit.lift_snd (Types.binaryProductLimit X Y) f g

/-- The published pairing has the uniqueness of Mathlib's full product cone. -/
theorem pairing_unique (T X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : T ⟶ X) (g : T ⟶ Y) (h : T ⟶ product X Y)
    (hfst : h ≫ fst X Y = f) (hsnd : h ≫ snd X Y = g) : h = pairing T X Y f g :=
  BinaryFan.IsLimit.hom_ext (Types.binaryProductLimit X Y)
    (hfst.trans (pairing_fst T X Y f g).symm) (hsnd.trans (pairing_snd T X Y f g).symm)

/-- The full universal cone of the exact registered coordinate family. This is the existing
binary product's mediator and universal property, indexed by its two declared coordinates.
Mathlib's `Fan.IsLimit.mk` changes only the discrete indexing presentation; the object, both
ordered legs, and the pairing are those already published above. -/
def componentIsLimit (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    IsLimit (Fan.mk (product X Y) (projection X Y)) := by
  refine Fan.IsLimit.mk _
    (fun s => pairing s.pt X Y (s.proj (0 : Fin 2)) (s.proj (1 : Fin 2))) ?_ ?_
  · intro s i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact pairing_fst _ X Y _ _
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      exact pairing_snd _ X Y _ _
  · intro s m h
    exact pairing_unique _ X Y _ _ m (h (0 : Fin 2)) (h (1 : Fin 2))

theorem map_apply (X X' Y Y' : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : X ⟶ X') (g : Y ⟶ Y') (p : product X Y) :
    map X X' Y Y' f g p = (f p.1, g p.2) := rfl

theorem map_id (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    map X X Y Y (𝟙 X) (𝟙 Y) = 𝟙 (product X Y) :=
  (Functor.uncurry.obj productDeclaration).map_id (X, Y)

theorem map_comp (X X' X'' Y Y' Y'' : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    map X X'' Y Y'' (f ≫ f') (g ≫ g') =
      map X X' Y Y' f g ≫ map X' X'' Y' Y'' f' g' :=
  (Functor.uncurry.obj productDeclaration).map_comp (f ×ₘ g) (f' ×ₘ g')

theorem map_fst (X X' Y Y' : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : X ⟶ X') (g : Y ⟶ Y') : map X X' Y Y' f g ≫ fst X' Y' = fst X Y ≫ f := rfl

theorem map_snd (X X' Y Y' : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : X ⟶ X') (g : Y ⟶ Y') : map X X' Y Y' f g ≫ snd X' Y' = snd X Y ≫ g := rfl

theorem iso_hom (X X' Y Y' : LeanCategories.Foundation.Mathlib.Sets.{u})
    (e : X ≅ X') (d : Y ≅ Y') : (iso X X' Y Y' e d).hom = map X X' Y Y' e.hom d.hom := rfl

theorem iso_inv (X X' Y Y' : LeanCategories.Foundation.Mathlib.Sets.{u})
    (e : X ≅ X') (d : Y ≅ Y') : (iso X X' Y Y' e d).inv = map X' X Y' Y e.inv d.inv := rfl

/-- The forward comparison preserves the supplied cone's first leg. -/
theorem coneComparison_hom_fst (X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (s : LimitCone (Limits.pair X Y)) :
    (coneComparison X Y s).hom ≫ s.cone.π.app ⟨WalkingPair.left⟩ = fst X Y :=
  (Types.binaryProductLimit X Y).conePointUniqueUpToIso_hom_comp s.isLimit ⟨WalkingPair.left⟩

/-- The forward comparison preserves the supplied cone's second leg. -/
theorem coneComparison_hom_snd (X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (s : LimitCone (Limits.pair X Y)) :
    (coneComparison X Y s).hom ≫ s.cone.π.app ⟨WalkingPair.right⟩ = snd X Y :=
  (Types.binaryProductLimit X Y).conePointUniqueUpToIso_hom_comp s.isLimit ⟨WalkingPair.right⟩

/-- The comparison's inverse is the actual ordered pairing of the supplied cone legs. -/
theorem coneComparison_inv (X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (s : LimitCone (Limits.pair X Y)) :
    (coneComparison X Y s).inv = pairing s.cone.pt X Y
      (s.cone.π.app ⟨WalkingPair.left⟩) (s.cone.π.app ⟨WalkingPair.right⟩) :=
  pairing_unique _ X Y _ _ _
    ((Types.binaryProductLimit X Y).conePointUniqueUpToIso_inv_comp s.isLimit ⟨WalkingPair.left⟩)
    ((Types.binaryProductLimit X Y).conePointUniqueUpToIso_inv_comp s.isLimit ⟨WalkingPair.right⟩)

/-- Transporting a pairing gives that cone's own universal mediator. -/
theorem pairing_coneComparison (T X Y : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : T ⟶ X) (g : T ⟶ Y) (s : LimitCone (Limits.pair X Y)) :
    pairing T X Y f g ≫ (coneComparison X Y s).hom = s.isLimit.lift (BinaryFan.mk f g) :=
  (Types.binaryProductLimit X Y).lift_comp_conePointUniqueUpToIso_hom s.isLimit

/-- At Mathlib's chosen limit, the general comparison is its existing natural comparison. -/
theorem coneComparison_chosen (X Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    coneComparison X Y ⟨limit.cone (Limits.pair X Y), limit.isLimit _⟩ =
      (chosenComparison.app X).app Y := by
  apply Iso.ext
  rfl

end Foundation.OrderedProducts

open Foundation.OrderedProducts

normalized_registry .functor
  { id := FunctorId.setsOrderedProduct
    source := Foundation.Sets, target := Constructed.EndofunctorsSets
    declaration := `CasCatalogue.Foundation.OrderedProducts.productDeclaration
    realization := `CasCatalogue.Foundation.OrderedProducts.productRealization
    expression := ProductExpr }

normalized_registry .object
  { id := ⟨"obj.sets.ordered_product"⟩, category := CategoryId.sets, name := "CartesianProduct"
    declaration := `CasCatalogue.Foundation.OrderedProducts.product
    components := some
      { arity := `CasCatalogue.Foundation.OrderedProducts.arity
        projection := `CasCatalogue.Foundation.OrderedProducts.projection
        isLimit := some `CasCatalogue.Foundation.OrderedProducts.componentIsLimit } }

normalized_registry .morphism
  { id := ⟨"mor.sets.product_projection"⟩, category := CategoryId.sets, name := "productProjection"
    declaration := `CasCatalogue.Foundation.OrderedProducts.projection }

normalized_registry .morphism
  { id := ⟨"mor.sets.product_fst"⟩, category := CategoryId.sets, name := "productFst"
    declaration := `CasCatalogue.Foundation.OrderedProducts.fst }

normalized_registry .morphism
  { id := ⟨"mor.sets.product_snd"⟩, category := CategoryId.sets, name := "productSnd"
    declaration := `CasCatalogue.Foundation.OrderedProducts.snd }

normalized_registry .morphism
  { id := ⟨"mor.sets.product_pair"⟩, category := CategoryId.sets, name := "productPair"
    declaration := `CasCatalogue.Foundation.OrderedProducts.pairing }

normalized_registry .morphism
  { id := ⟨"mor.sets.product_map"⟩, category := CategoryId.sets, name := "productMap"
    declaration := `CasCatalogue.Foundation.OrderedProducts.map }

normalized_registry .presentation
  { id := ⟨"cmp.sets.product_iso"⟩, name := "productIso"
    source := ⟨"obj.sets.ordered_product"⟩, target := ⟨"obj.sets.ordered_product"⟩
    declaration := `CasCatalogue.Foundation.OrderedProducts.iso }

end CasCatalogue
