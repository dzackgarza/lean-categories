/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Freely adjoining degeneracies to a semisimplicial object

Weibel, *An Introduction to Homological Algebra* (1994), §8.1, pp. 254--258
(FC05-C08-U011).

The inclusion of the semi-simplex category into the simplex category induces a
restriction functor from simplicial to semisimplicial objects.  Its left
adjoint is the left Kan extension along the opposite inclusion.

Weibel's explicit degreewise formula as a finite coproduct indexed by
surjections `[n] ↠ [p]` is the pointwise computation of this Kan extension; its
identification uses the simplex epi--mono factorization and is theorem-layer
content here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Simplicial

universe v u

variable (C : Type u) [Category.{v} C]

/-- Semisimplicial objects in `C`. -/
abbrev SemisimplicialObject := SemiSimplexCategoryᵒᵖ ⥤ C

/-- The opposite inclusion used to forget degeneracies. -/
def semiSimplexInclusionOp : SemiSimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ :=
  SemiSimplexCategory.toSimplexCategory.op

/-- Restriction of a simplicial object to its semisimplicial faces. -/
def forgetDegeneracies : (SimplicialObject C) ⥤ SemisimplicialObject C :=
  (Functor.whiskeringLeft _ _ C).obj (semiSimplexInclusionOp)

variable [∀ K : SemisimplicialObject C,
  (semiSimplexInclusionOp).HasLeftKanExtension K]

/-- The free simplicial object obtained by adjoining degeneracies to a
semisimplicial object: left Kan extension along the semisimplex inclusion. -/
def freelyAddDegeneracies : SemisimplicialObject C ⥤ SimplicialObject C :=
  (semiSimplexInclusionOp).lan

/-- The free-degeneracy construction is left adjoint to forgetting
degeneracies. -/
def freelyAddDegeneraciesAdjunction :
    freelyAddDegeneracies C ⊣ forgetDegeneracies C :=
  (semiSimplexInclusionOp).lanAdjunction C

end LeanCategories.Homological
