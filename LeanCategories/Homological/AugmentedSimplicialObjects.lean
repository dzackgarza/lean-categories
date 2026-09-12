/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SimplicialChainComplexes
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# Aspherical and contractible augmented simplicial objects

Weibel, *An Introduction to Homological Algebra* (1994), Definition 8.4.6,
pp. 270--274 (FC05-C08-U049).

The left contractibility convention is Mathlib's extra degeneracy `σ_{-1}`.
The right convention is obtained by reversing the simplex category.  Asphericity
is stated directly in terms of normalized homology and the augmentation on `π₀`.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- Reverse the simplex ordering of an augmented simplicial object, leaving its
augmentation point unchanged. -/
def reverseAugmented (X : SimplicialObject.Augmented C) :
    SimplicialObject.Augmented C where
  left := SimplicialObject.opFunctor.obj X.left
  right := X.right
  hom := SimplicialObject.opFunctor.map X.hom

/-- Weibel's left contractibility condition: existence of an extra degeneracy
on the left of the ordinary degeneracies. -/
def IsLeftContractible (X : SimplicialObject.Augmented C) : Prop :=
  Nonempty (SimplicialObject.Augmented.ExtraDegeneracy X)

/-- Weibel's right contractibility condition, obtained from left contractibility
after reversing the simplex ordering. -/
def IsRightContractible (X : SimplicialObject.Augmented C) : Prop :=
  IsLeftContractible (reverseAugmented X)

variable [Abelian C]

/-- The augmentation from the normalized Moore complex to the augmentation point
concentrated in degree zero. -/
noncomputable def normalizedAugmentation (X : SimplicialObject.Augmented C) :
    simplicialNormalizedChainComplex X.left ⟶ (ChainComplex.single₀ C).obj X.right :=
  AlgebraicTopology.inclusionOfMooreComplexMap X.left ≫
    AlgebraicTopology.AlternatingFaceMapComplex.ε.app X

/-- An augmented simplicial object is aspherical when its positive homotopy
objects vanish and its augmentation induces an isomorphism on `π₀`. -/
def IsAspherical (X : SimplicialObject.Augmented C) : Prop :=
  (∀ n : ℕ, 0 < n → IsZero (simplicialHomotopyObject X.left n)) ∧
    IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) 0).map
      (normalizedAugmentation X))

end LeanCategories.Homological
