/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas
public meta import LeanCategories.Catalogue.Semantics.Modules.Catalogue

@[expose] public section

/-!
# Arrows and evaluation of elements of an automorphism group

For a category `C` and its selected object `X`, an element of the existing
`Aut(X)` is the complete isomorphism `X ≅ X`. Its forward and inverse arrows
remain morphisms of `C`. Projecting these arrows does not replace an
automorphism of a structured object by an arbitrary permutation of its carrier.

For any selected functor `U : C ⥤ Sets`, these arrows act on `U(X)` through
`U.map`. The public evaluation families retain `C`, `U`, and `X` explicitly.
They use the original automorphism-group multiplication, whose action is
function composition: `(a * b)(x) = a(b(x))`. The two projection families are
also registered at each existing concrete `Aut` owner: sets, groups, and
modules over a selected ring. The returned arrows are whole callable maps.

The conjugation equations below hold for every isomorphism in every category.
They expose Mathlib's actual `Aut.autMulEquivOfIso`, including its inverse
arrow, and do not select a new transport or a new automorphism.

Sources: Mathlib `CategoryTheory.Aut`, `Aut.toEnd`,
`Aut.autMulEquivOfIso`, `Functor.mapIso`, and the existing
`Automorphisms.automorphismsConstruction`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.AutomorphismArrows

universe u v

/-- The actual forward morphism of `a : Aut X`, in the selected category `C`.
Here `Aut X` is the carrier of `automorphismsConstruction C` at `Core.mk X`.
The result is an endomorphism of `X`, with all of `X`'s chosen structure. -/
def forward (C : Cat.{v, u}) (X : C) (a : Aut X) : X ⟶ X := a.hom

/-- The actual inverse morphism of the same automorphism element, with source
and target the original selected object `X` of `C`. -/
def backward (C : Cat.{v, u}) (X : C) (a : Aut X) : X ⟶ X := a.inv

theorem forward_backward (C : Cat.{v, u}) (X : C) (a : Aut X) :
    forward C X a ≫ backward C X a = 𝟙 X := a.hom_inv_id

theorem backward_forward (C : Cat.{v, u}) (X : C) (a : Aut X) :
    backward C X a ≫ forward C X a = 𝟙 X := a.inv_hom_id

/-- Projection agrees with the existing inverse in the automorphism group. -/
theorem forward_inv (C : Cat.{v, u}) (X : C) (a : Aut X) :
    forward C X a⁻¹ = backward C X a := rfl

/-- Projection agrees with the existing multiplication in the automorphism group. -/
theorem forward_mul (C : Cat.{v, u}) (X : C) (a b : Aut X) :
    forward C X (a * b) = forward C X b ≫ forward C X a := rfl

/-- The forward arrow of the actual conjugated automorphism, on the whole object. -/
theorem forward_conjugate (C : Cat.{v, u}) (X Y : C) (e : X ≅ Y) (a : Aut X) :
    forward C Y
        ((Automorphisms.automorphismsConstruction C).map
          (show Core.mk X ⟶ Core.mk Y from CoreHom.mk e) a) =
      e.inv ≫ forward C X a ≫ e.hom := rfl

/-- The inverse arrow of that same conjugated automorphism. -/
theorem backward_conjugate (C : Cat.{v, u}) (X Y : C) (e : X ≅ Y) (a : Aut X) :
    backward C Y
        ((Automorphisms.automorphismsConstruction C).map
          (show Core.mk X ⟶ Core.mk Y from CoreHom.mk e) a) =
      e.inv ≫ backward C X a ≫ e.hom := rfl

/-- For an arbitrary selected category `C`, functor `U : C ⥤ Type v`, and
object `X : C`, the map `Aut(X) × U(X) → U(X)` with action
`(a, x) ↦ U.map a.hom x`. It is evaluation of the actual image isomorphism
`U.mapIso a`, so its source retains the original automorphism group of `X`.
No faithfulness, finiteness, choice of coordinates, or concrete-category
hypothesis is required. The hom-set and set universes here are both `v`. -/
def evaluation (C : Cat.{v, u}) (U : C ⥤ Type v) (X : C) :
    (Aut X × U.obj X : Type v) ⟶ U.obj X :=
  TypeCat.ofHom fun p => (U.mapIso p.1).hom p.2

/-- Inverse evaluation for the same selected `C`, `U`, and `X`:
`(a, x) ↦ U.map a.inv x`. This projects the inverse direction of `a`,
without computing or selecting a replacement isomorphism. -/
def inverseEvaluation (C : Cat.{v, u}) (U : C ⥤ Type v) (X : C) :
    (Aut X × U.obj X : Type v) ⟶ U.obj X :=
  TypeCat.ofHom fun p => (U.mapIso p.1).inv p.2

theorem evaluation_apply (C : Cat.{v, u}) (U : C ⥤ Type v) (X : C)
    (a : Aut X) (x : U.obj X) :
    evaluation C U X (a, x) = U.map (forward C X a) x := rfl

theorem inverseEvaluation_apply (C : Cat.{v, u}) (U : C ⥤ Type v) (X : C)
    (a : Aut X) (x : U.obj X) :
    inverseEvaluation C U X (a, x) = U.map (backward C X a) x := rfl

theorem evaluation_one (C : Cat.{v, u}) (U : C ⥤ Type v) (X : C) (x : U.obj X) :
    evaluation C U X (1, x) = x := by
  change U.map (𝟙 X) x = x
  rw [U.map_id]
  rfl

theorem evaluation_mul (C : Cat.{v, u}) (U : C ⥤ Type v) (X : C)
    (a b : Aut X) (x : U.obj X) :
    evaluation C U X (a * b, x) =
      evaluation C U X (a, evaluation C U X (b, x)) := by
  change U.map (b.hom ≫ a.hom) x = U.map a.hom (U.map b.hom x)
  rw [U.map_comp]
  rfl

theorem evaluation_inverseEvaluation (C : Cat.{v, u}) (U : C ⥤ Type v)
    (X : C) (a : Aut X) (x : U.obj X) :
    evaluation C U X (a, inverseEvaluation C U X (a, x)) = x :=
  Iso.inv_hom_id_apply (U.mapIso a) x

theorem inverseEvaluation_evaluation (C : Cat.{v, u}) (U : C ⥤ Type v)
    (X : C) (a : Aut X) (x : U.obj X) :
    inverseEvaluation C U X (a, evaluation C U X (a, x)) = x :=
  Iso.hom_inv_id_apply (U.mapIso a) x

/-- The forward set map carried by an element of the selected symmetric group. -/
def setsForward (X : Type u) (a : (Automorphisms.automorphisms (Type u)).obj ⟨X⟩) :
    X ⟶ X := forward (Cat.of (Type u)) X a

/-- The inverse set map carried by that same element of the symmetric group. -/
def setsBackward (X : Type u) (a : (Automorphisms.automorphisms (Type u)).obj ⟨X⟩) :
    X ⟶ X := backward (Cat.of (Type u)) X a

/-- The forward group homomorphism of an element of `Aut(G)` in `Groups`.
Its whole function is callable on every element of the original group `G`. -/
def groupsForward (G : GrpCat.{u}) (a : (Automorphisms.automorphisms GrpCat).obj ⟨G⟩) :
    G ⟶ G := forward (Cat.of GrpCat.{u}) G a

/-- The inverse group homomorphism of the same `Aut(G)` element. -/
def groupsBackward (G : GrpCat.{u}) (a : (Automorphisms.automorphisms GrpCat).obj ⟨G⟩) :
    G ⟶ G := backward (Cat.of GrpCat.{u}) G a

/-- The forward `R`-linear map of an element of `Aut(M)` for the selected
`R : RingCat` and `M : ModuleCat R`. It retains that exact scalar action. -/
def modulesForward (R : RingCat.{u}) (M : ModuleCat.{u} R)
    (a : (Automorphisms.automorphisms (ModuleCat.{u} R)).obj ⟨M⟩) : M ⟶ M :=
  forward (Cat.of (ModuleCat.{u} R)) M a

/-- The inverse `R`-linear map of that same automorphism element. -/
def modulesBackward (R : RingCat.{u}) (M : ModuleCat.{u} R)
    (a : (Automorphisms.automorphisms (ModuleCat.{u} R)).obj ⟨M⟩) : M ⟶ M :=
  backward (Cat.of (ModuleCat.{u} R)) M a

end CasCatalogue.Algebra.AutomorphismArrows

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.sets.automorphism_forward"⟩, category := CategoryId.sets
    name := "automorphism_forward"
    declaration := `CasCatalogue.Algebra.AutomorphismArrows.setsForward }
normalized_registry .morphism
  { id := ⟨"mor.sets.automorphism_backward"⟩, category := CategoryId.sets
    name := "automorphism_backward"
    declaration := `CasCatalogue.Algebra.AutomorphismArrows.setsBackward }
normalized_registry .morphism
  { id := ⟨"mor.groups.automorphism_forward"⟩, category := CategoryId.groups
    name := "automorphism_forward"
    declaration := `CasCatalogue.Algebra.AutomorphismArrows.groupsForward }
normalized_registry .morphism
  { id := ⟨"mor.groups.automorphism_backward"⟩, category := CategoryId.groups
    name := "automorphism_backward"
    declaration := `CasCatalogue.Algebra.AutomorphismArrows.groupsBackward }
normalized_registry .morphism
  { id := ⟨"mor.modules.automorphism_forward"⟩, category := CategoryId.modulesR
    name := "automorphism_forward"
    declaration := `CasCatalogue.Algebra.AutomorphismArrows.modulesForward }
normalized_registry .morphism
  { id := ⟨"mor.modules.automorphism_backward"⟩, category := CategoryId.modulesR
    name := "automorphism_backward"
    declaration := `CasCatalogue.Algebra.AutomorphismArrows.modulesBackward }
normalized_registry .morphism
  { id := ⟨"mor.sets.automorphism_evaluation"⟩, category := CategoryId.sets
    name := "automorphism_evaluation"
    declaration := `CasCatalogue.Algebra.AutomorphismArrows.evaluation }
normalized_registry .morphism
  { id := ⟨"mor.sets.automorphism_inverse_evaluation"⟩, category := CategoryId.sets
    name := "automorphism_inverse_evaluation"
    declaration := `CasCatalogue.Algebra.AutomorphismArrows.inverseEvaluation }

end CasCatalogue
