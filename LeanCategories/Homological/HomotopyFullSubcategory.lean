/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Full subcategories of the homotopy category

Weibel, *An Introduction to Homological Algebra*, §10.1, pp. 369--372
(FC05-C10-U003).

A full subcategory of complexes determines the full subcategory of the homotopy category on the
same objects.  Mathlib's `HomotopyCategory` already quotients chain maps by chain homotopy, so the
Hom sets of this full subcategory are automatically the source quotients.  The statement that this
subcategory is additive under closure hypotheses is theorem-level.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Homological

universe u v w

variable {ι : Type w}
variable (V : Type u) [Category.{v} V] [Preadditive V]
variable (c : ComplexShape ι)

/-- The full subcategory of `K(V,c)` determined by an object property on complexes.

Source: Weibel, §10.1, pp. 369--372 (FC05-C10-U003). -/
abbrev HomotopyFullSubcategory
    (P : ObjectProperty (HomologicalComplex V c)) :=
  ObjectProperty.FullSubcategory
    (fun K : HomotopyCategory V c => P K.as)

end LeanCategories.Homological

namespace LeanCategories.Homological

open HomologicalComplex

variable (V : Type u) [Category.{v} V] [Preadditive V]

/-- A cochain complex is bounded below when it is strictly supported in degrees `≥ n` for some
integer `n`. -/
def IsCochainBoundedBelow (K : CochainComplex V ℤ) : Prop :=
  ∃ n : ℤ, K.IsStrictlyGE n

/-- A cochain complex is bounded above when it is strictly supported in degrees `≤ n` for some
integer `n`. -/
def IsCochainBoundedAbove (K : CochainComplex V ℤ) : Prop :=
  ∃ n : ℤ, K.IsStrictlyLE n

/-- A cochain complex is bounded when it is bounded both below and above. -/
def IsCochainBounded (K : CochainComplex V ℤ) : Prop :=
  IsCochainBoundedBelow V K ∧ IsCochainBoundedAbove V K

/-- Weibel's `K⁺(V)`: bounded-below cochain complexes up to chain homotopy.

Source: Weibel, §10.1, pp. 369--372 (FC05-C10-U004). -/
abbrev HomotopyCategoryPlus :=
  HomotopyFullSubcategory V (.up ℤ) (IsCochainBoundedBelow V)

/-- Weibel's `K⁻(V)`: bounded-above cochain complexes up to chain homotopy.

Source: Weibel, §10.1, pp. 369--372 (FC05-C10-U004). -/
abbrev HomotopyCategoryMinus :=
  HomotopyFullSubcategory V (.up ℤ) (IsCochainBoundedAbove V)

/-- Weibel's `Kᵇ(V)`: bounded cochain complexes up to chain homotopy.

Source: Weibel, §10.1, pp. 369--372 (FC05-C10-U004). -/
abbrev HomotopyCategoryBounded :=
  HomotopyFullSubcategory V (.up ℤ) (IsCochainBounded V)

end LeanCategories.Homological
