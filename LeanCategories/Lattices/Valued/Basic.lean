/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- The objects that are finite projective and have a symmetric form. -/
def isLattice : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ Module.Finite R L.carrier ∧ Module.Projective R L.carrier ∧ L.IsSymmetric

/-- The category of `W`-valued `R`-lattices. -/
abbrev LatticeCat := (isLattice R W).FullSubcategory

/-- Finite symmetric form modules. Projectivity is not required. -/
def isFiniteForm : ObjectProperty (BilinModuleCat R W) :=
  fun L ↦ Module.Finite R L.carrier ∧ L.IsSymmetric

/-- The category of finite `W`-valued symmetric form modules. -/
abbrev FiniteFormCat := (isFiniteForm R W).FullSubcategory

/-- Integral lattices are `R`-valued `R`-lattices. -/
abbrev IntegralLatticeCat := LatticeCat R R

end LeanCategories.Lattices.Valued

