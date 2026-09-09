/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.PEmpty

@[expose] public section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace LeanCategories.CategoryTheory

universe v u w

/-- Riehl's definition of a category of models for an algebraic theory: a category admitting a
finitary monadic functor to `Set` (FC03-C05-U037).  Here “finitary” is expressed by preservation
of filtered colimits, and “monadic” by Mathlib's `MonadicRightAdjoint` structure. -/
def IsCategoryOfModelsForAlgebraicTheory
    (A : Type u) [_root_.CategoryTheory.Category.{v} A] : Prop :=
  ∃ U : A ⥤ Type w,
    Nonempty (_root_.CategoryTheory.MonadicRightAdjoint U) ∧
      _root_.CategoryTheory.Limits.PreservesFilteredColimits U

/-- Eilenberg–Moore algebras of a finitary monad form a category of models for an algebraic
 theory: monadicity of the forgetful functor is canonical, so only finitarity is an assumption.
 This is the positive acceptance model for FC03-C05-U037. -/
theorem isCategoryOfModels_monadAlgebras
    (T : _root_.CategoryTheory.Monad (Type w))
    [_root_.CategoryTheory.Limits.PreservesFilteredColimits T.forget] :
    IsCategoryOfModelsForAlgebraicTheory.{w,w+1,w} T.Algebra := by
  refine ⟨T.forget, ⟨inferInstance⟩, ?_⟩
  infer_instance

/-- The empty category is not a category of models for an algebraic theory.  A monadic functor
`U : Discrete PEmpty ⥤ Type` would be a right adjoint, hence would have a left adjoint; evaluating
that left adjoint at any set would produce an impossible object of `Discrete PEmpty`.
This is the separating acceptance example for FC03-C05-U037. -/
theorem not_isCategoryOfModels_empty :
    ¬ IsCategoryOfModelsForAlgebraicTheory.{0,0,w} (_root_.CategoryTheory.Discrete PEmpty) := by
  intro h
  rcases h with ⟨U, ⟨hmon⟩, _⟩
  exact (hmon.L.obj PUnit).as.elim

end LeanCategories.CategoryTheory
