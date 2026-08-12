/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Completion
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Arithmetic-place realizations of number-field lattices

Mathlib supplies separate finite and infinite place types. This file uses their sum as one
index for lattice realizations. Finite integral realizations use completed local integer rings.
Infinite realizations use the field completion.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open IsDedekindDomain NumberField
open scoped NumberField

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A finite or infinite place of a number field. The summands retain their different
arithmetic meanings. -/
abbrev ArithmeticPlace := FinitePlace K ⊕ InfinitePlace K

namespace ArithmeticPlace

/-- The height-one point which owns a finite place. -/
def finiteHeightOne (v : FinitePlace K) : HeightOneSpectrum (𝓞 K) :=
  v.maximalIdeal

/-- Finite places are equivalent to height-one points of the ring of integers. -/
def finiteEquivHeightOneSpectrum :
    FinitePlace K ≃ HeightOneSpectrum (𝓞 K) :=
  FinitePlace.equivHeightOneSpectrum

/-- The local field at an arithmetic place. -/
abbrev FieldCompletion : ArithmeticPlace K → Type u
  | Sum.inl v => (finiteHeightOne K v).adicCompletion K
  | Sum.inr v => v.Completion

/-- The coefficient ring for an integral lattice at an arithmetic place.
At a finite place this is the completed integer ring. At an infinite place it is the field. -/
abbrev IntegralCoefficient : ArithmeticPlace K → Type u
  | Sum.inl v => (finiteHeightOne K v).adicCompletionIntegers K
  | Sum.inr v => v.Completion

noncomputable instance integralCoefficientCommRing (v : ArithmeticPlace K) :
    CommRing (IntegralCoefficient K v) := by
  cases v <;> infer_instance

noncomputable instance integralCoefficientAlgebra (v : ArithmeticPlace K) :
    Algebra (𝓞 K) (IntegralCoefficient K v) := by
  cases v <;> infer_instance

noncomputable instance fieldCompletionCommRing (v : ArithmeticPlace K) :
    CommRing (FieldCompletion K v) := by
  cases v <;> infer_instance

noncomputable instance fieldCompletionAlgebra (v : ArithmeticPlace K) :
    Algebra (𝓞 K) (FieldCompletion K v) := by
  cases v <;> infer_instance

/-- Realize an integral lattice at a finite or infinite arithmetic place. -/
def integralRealization (v : ArithmeticPlace K) :
    IntegralLatticeCat (𝓞 K) ⥤ IntegralLatticeCat (IntegralCoefficient K v) :=
  match v with
  | Sum.inl w => completeIntegralAtHeightOne (𝓞 K) K (finiteHeightOne K w)
  | Sum.inr w => baseChangeIntegral (𝓞 K) w.Completion

/-- Realize a finite projective integral lattice at an arithmetic place. -/
def finiteProjectiveRealization (v : ArithmeticPlace K) :
    FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K) ⥤
      FiniteProjectiveLatticeCat (IntegralCoefficient K v) (IntegralCoefficient K v) :=
  match v with
  | Sum.inl w => completeFiniteIntegralAtHeightOne (𝓞 K) K (finiteHeightOne K w)
  | Sum.inr w => baseChangeFiniteIntegral (𝓞 K) w.Completion

/-- Extend an integral lattice to the local field at an arithmetic place. -/
def fieldRealization (v : ArithmeticPlace K) :
    IntegralLatticeCat (𝓞 K) ⥤ IntegralLatticeCat (FieldCompletion K v) :=
  match v with
  | Sum.inl w => extendIntegralToHeightOneField (𝓞 K) K (finiteHeightOne K w)
  | Sum.inr w => baseChangeIntegral (𝓞 K) w.Completion

/-- Extend a finite projective integral lattice to the local field at an arithmetic place. -/
def finiteProjectiveFieldRealization (v : ArithmeticPlace K) :
    FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K) ⥤
      FiniteProjectiveLatticeCat (FieldCompletion K v) (FieldCompletion K v) :=
  match v with
  | Sum.inl w => extendFiniteIntegralToHeightOneField (𝓞 K) K (finiteHeightOne K w)
  | Sum.inr w => baseChangeFiniteIntegral (𝓞 K) w.Completion

@[simp]
theorem integralRealization_finite (v : FinitePlace K) :
    integralRealization K (Sum.inl v) =
      completeIntegralAtHeightOne (𝓞 K) K (finiteHeightOne K v) :=
  rfl

@[simp]
theorem integralRealization_infinite (v : InfinitePlace K) :
    integralRealization K (Sum.inr v) = baseChangeIntegral (𝓞 K) v.Completion :=
  rfl

@[simp]
theorem fieldRealization_finite (v : FinitePlace K) :
    fieldRealization K (Sum.inl v) =
      extendIntegralToHeightOneField (𝓞 K) K (finiteHeightOne K v) :=
  rfl

@[simp]
theorem fieldRealization_infinite (v : InfinitePlace K) :
    fieldRealization K (Sum.inr v) = baseChangeIntegral (𝓞 K) v.Completion :=
  rfl

end ArithmeticPlace

end LeanCategories.Lattices.Valued
