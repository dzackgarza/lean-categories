/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.DiagonalizableGroupData
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Tori relative to a field of definition

Definition-level realization of Humphreys FC16-C12-U019.

The ambient algebraic group is kept over the algebraic closure K, as in the
preceding FC16 algebraic-group layer. The general-field layer supplies two
descent predicates:

* whether the torus itself is defined over the chosen base field k;
* which characters of the base-changed torus are defined over k.

With those inputs, the source definitions are direct. A k-torus is a torus
defined over k; it is k-split when the k-defined characters span its
coordinate algebra, and k-anisotropic when no nontrivial character is
defined over k.

The equivalent description of a split torus as a k-form of a power of G_m,
and the later split/anisotropic decomposition theorem, are result content
and are not included in Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

/-- A torus over the algebraic closure together with the assertion, supplied
by the preceding descent layer, that it is defined over the base field. -/
def IsBaseFieldTorusData
    {K : Type u} [Field K] [IsAlgClosed K]
    (isDefinedOverBase : AffineAlgebraicGroup K → Prop)
    (T : AffineAlgebraicGroup K) : Prop :=
  IsTorusData T ∧ isDefinedOverBase T

/-- Values in K[T] of the characters supplied as defined over the base
field. -/
noncomputable def baseDefinedCharacterValuesData
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : AffineAlgebraicGroup K)
    (isDefinedOverBaseCharacter :
      GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra T) → Prop) :
    Set (AffineAlgebraicGroup.coordinateHopfAlgebra T) :=
  {f | ∃ chi, isDefinedOverBaseCharacter chi ∧ f = chi.val}

/-- A k-torus is split when its k-defined characters span its coordinate
algebra. -/
noncomputable def IsBaseFieldSplitTorusData
    {K : Type u} [Field K] [IsAlgClosed K]
    (isDefinedOverBase : AffineAlgebraicGroup K → Prop)
    (T : AffineAlgebraicGroup K)
    (isDefinedOverBaseCharacter :
      GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra T) → Prop) : Prop :=
  IsBaseFieldTorusData isDefinedOverBase T ∧
    Submodule.span K
      (baseDefinedCharacterValuesData T isDefinedOverBaseCharacter) = ⊤

/-- A k-torus is anisotropic when it has no nontrivial character defined
over k. -/
def IsBaseFieldAnisotropicTorusData
    {K : Type u} [Field K] [IsAlgClosed K]
    (isDefinedOverBase : AffineAlgebraicGroup K → Prop)
    (T : AffineAlgebraicGroup K)
    (isDefinedOverBaseCharacter :
      GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra T) → Prop) : Prop :=
  IsBaseFieldTorusData isDefinedOverBase T ∧
    ∀ chi, isDefinedOverBaseCharacter chi → chi = 1

/-- The complete base-field torus datum used in Humphreys: the values of
base-defined characters together with the k-torus, k-split, and k-anisotropic
conditions computed from the same descent inputs. -/
structure BaseFieldTorusData
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : AffineAlgebraicGroup K) where
  characterValues : Set (AffineAlgebraicGroup.coordinateHopfAlgebra T)
  isTorus : Prop
  isSplit : Prop
  isAnisotropic : Prop

/-- Construct the base-field torus notions from the supplied field-of-definition
predicates. -/
noncomputable def baseFieldTorusData
    {K : Type u} [Field K] [IsAlgClosed K]
    (isDefinedOverBase : AffineAlgebraicGroup K → Prop)
    (T : AffineAlgebraicGroup K)
    (isDefinedOverBaseCharacter :
      GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra T) → Prop) :
    BaseFieldTorusData T where
  characterValues :=
    baseDefinedCharacterValuesData T isDefinedOverBaseCharacter
  isTorus := IsBaseFieldTorusData isDefinedOverBase T
  isSplit :=
    IsBaseFieldSplitTorusData isDefinedOverBase T isDefinedOverBaseCharacter
  isAnisotropic :=
    IsBaseFieldAnisotropicTorusData isDefinedOverBase T isDefinedOverBaseCharacter

end LeanCategories.AlgebraicGeometry
