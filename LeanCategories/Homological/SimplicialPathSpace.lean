/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Simplicial path spaces

Weibel, *An Introduction to Homological Algebra*, Construction 8.3.14, pp. 263--269
(FC05-C08-U042).

The path-space index functor adjoins a new initial element to every simplex ordinal.  Mathlib's
monoidal structure on the augmented simplex category is ordinal sum, so tensoring on the left by
`[0]` gives this endofunctor without rebuilding the ordinal combinatorics.  Precomposition on
simplicial objects therefore has `(PA)_n = A_{n+1}`.  The canonical inclusion of the old ordinal
as the second summand gives Weibel's `∂₀ : PA ⟶ A`.
-/

@[expose] public section

open CategoryTheory
open Simplicial
open AugmentedSimplexCategory

namespace LeanCategories.Homological

/-- The simplex-category endofunctor `[n] ↦ [n+1]` obtained by adjoining a new initial element.

Source: Weibel, Construction 8.3.14, pp. 263--269 (FC05-C08-U042). -/
def pathIndex : SimplexCategory ⥤ SimplexCategory where
  obj n := tensorObjOf ⦋0⦌ n
  map f := tensorHomOf (𝟙 ⦋0⦌) f
  map_id X := by
    exact congrArg WithInitial.down (tensor_id (.of ⦋0⦌) (.of X))
  map_comp f g := by
    exact (congrArg WithInitial.down
      (tensorHom_comp_tensorHom (𝟙 (WithInitial.of ⦋0⦌)) (WithInitial.incl.map f)
        (𝟙 (WithInitial.of ⦋0⦌)) (WithInitial.incl.map g))).symm

/-- The natural inclusion `[n] ⟶ [n+1]` selecting the old ordinal after the new initial element. -/
def pathIndexUnit : 𝟭 SimplexCategory ⟶ pathIndex where
  app X := inr' ⦋0⦌ X
  naturality X Y f := by
    exact (congrArg WithInitial.down
      (inr_comp_tensorHom (𝟙 (WithInitial.of ⦋0⦌)) (WithInitial.incl.map f))).symm

/-- The opposite natural transformation used to obtain the face map `∂₀ : PA ⟶ A`. -/
def pathIndexOpUnit : pathIndex.op ⟶ 𝟭 (SimplexCategoryᵒᵖ) where
  app X := (pathIndexUnit.app X.unop).op
  naturality X Y f := by
    apply Quiver.Hom.unop_inj
    simpa using (pathIndexUnit.naturality f.unop).symm

universe u v

variable (C : Type u) [Category.{v} C]

/-- Weibel's simplicial path-space functor.  In degree `n`, `(PA)_n = A_{n+1}`.

Source: Weibel, Construction 8.3.14, pp. 263--269 (FC05-C08-U042). -/
def pathSpaceFunctor : SimplicialObject C ⥤ SimplicialObject C :=
  (Functor.whiskeringLeft _ _ C).obj pathIndex.op

/-- The natural simplicial map `∂₀ : PA ⟶ A` induced by deleting the newly adjoined initial
vertex.

Source: Weibel, Construction 8.3.14, pp. 263--269 (FC05-C08-U042). -/
def pathFaceZero : pathSpaceFunctor C ⟶ 𝟭 (SimplicialObject C) :=
  (Functor.whiskeringLeft (SimplexCategoryᵒᵖ) (SimplexCategoryᵒᵖ) C).map pathIndexOpUnit

end LeanCategories.Homological
