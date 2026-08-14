/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.FilteredAlgebra.Basic

/-!
# Associated graded rings and modules

This file gives the quotient components of the associated graded constructions.
The filtration conventions are Mathlib's increasing `IsRingFiltration` and
`IsModuleFiltration` conventions. The component in degree `n` is
`F n / F_lt n`, where `F_lt n` is the lower-filtration term.

The terminology follows Atiyah--Macdonald, *Introduction to Commutative
Algebra*, Chapter 10, ``The associated graded ring'', pp. 111--112. Mathlib's
`FilteredAlgebra.Basic`, `LinearMap.liftQ₂`, and `DirectSum` provide the
underlying filtration, quotient, and graded-sum infrastructure.

This module does not use the Rees algebra as a substitute for the associated
graded object.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v w

section Ring

variable {R : Type u} [CommRing R]

/-- The lower-filtration submodule inside the degree-`n` term. -/
abbrev associatedGradedRingLower (F F_lt : ℕ → Submodule ℤ R) (n : ℕ) :
    Submodule ℤ (F n) :=
  (F_lt n).comap (F n).subtype

/-!
`IsRingFiltration` records multiplication of filtration terms. The extra
condition below records the lower-term stability needed to descend that
multiplication to quotient components.
-/
class IsAssociatedGradedRingFiltration
    (F F_lt : ℕ → Submodule ℤ R) [IsRingFiltration F F_lt] : Prop where
  lower_mul_left : ∀ {i j : ℕ} {x : R}, x ∈ F_lt i →
    ∀ {y : R}, y ∈ F j → x * y ∈ F_lt (i + j)

/-- The degree-`n` component of the associated graded ring. -/
abbrev associatedGradedRingComponent (F F_lt : ℕ → Submodule ℤ R) (n : ℕ) :=
  (F n) ⧸ associatedGradedRingLower F F_lt n

/-- The additive direct sum of the associated graded ring components. -/
abbrev associatedGradedRing (F F_lt : ℕ → Submodule ℤ R) :=
  ⨁ n, associatedGradedRingComponent F F_lt n

/-- The canonical map from a filtration term to its associated graded component. -/
abbrev associatedGradedRingMk (F F_lt : ℕ → Submodule ℤ R) (n : ℕ) :
    F n →ₗ[ℤ] associatedGradedRingComponent F F_lt n :=
  (associatedGradedRingLower F F_lt n).mkQ

private noncomputable def filteredRingMul (F : ℕ → Submodule ℤ R) (i j : ℕ) :
    F i →ₗ[ℤ] F j →ₗ[ℤ] F (i + j) :=
  LinearMap.mk₂ ℤ
    (fun x y =>
      (⟨(x : R) * (y : R), SetLike.GradedMonoid.toGradedMul.mul_mem x.2 y.2⟩ : F (i + j)))
    (fun x₁ x₂ y => by ext; simp [mul_add])
    (fun c x y => by ext; simp [smul_eq_mul, mul_assoc])
    (fun x y₁ y₂ => by ext; simp [add_mul])
    (fun c x y => by ext; simp [smul_eq_mul, mul_assoc])

/-- Multiplication of homogeneous associated-graded components.

The lower-filtration condition is exactly the quotient-descent condition.
-/
noncomputable def associatedGradedRingMul
    (F F_lt : ℕ → Submodule ℤ R) [IsRingFiltration F F_lt]
    [IsAssociatedGradedRingFiltration F F_lt] (i j : ℕ) :
    associatedGradedRingComponent F F_lt i →ₗ[ℤ]
      associatedGradedRingComponent F F_lt j →ₗ[ℤ]
        associatedGradedRingComponent F F_lt (i + j) := by
  apply LinearMap.liftQ₂
    (associatedGradedRingLower F F_lt i)
    (associatedGradedRingLower F F_lt j)
    (filteredRingMul F i j)
  · intro x hx
    apply LinearMap.ext
    intro y
    apply (Submodule.Quotient.mk_eq_zero).2
    exact IsAssociatedGradedRingFiltration.lower_mul_left hx y.2
  · intro y hy
    apply LinearMap.ext
    intro x
    apply (Submodule.Quotient.mk_eq_zero).2
    simpa [mul_comm] using IsAssociatedGradedRingFiltration.lower_mul_left hy x.2

@[simp]
theorem associatedGradedRingMul_mk (F F_lt : ℕ → Submodule ℤ R)
    [IsRingFiltration F F_lt] [IsAssociatedGradedRingFiltration F F_lt]
    (i j : ℕ) (x : F i) (y : F j) :
    associatedGradedRingMul F F_lt i j
        (associatedGradedRingMk F F_lt i x)
        (associatedGradedRingMk F F_lt j y) =
      associatedGradedRingMk F F_lt (i + j) (filteredRingMul F i j x y) :=
  rfl

end Ring

section Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The lower-filtration submodule inside a degree-`n` module term. -/
abbrev associatedGradedModuleLower (F F_lt : ℕ → Submodule R M) (n : ℕ) :
    Submodule R (F n) :=
  (F_lt n).comap (F n).subtype

/-- The degree-`n` component of the associated graded module. -/
abbrev associatedGradedModuleComponent (F F_lt : ℕ → Submodule R M) (n : ℕ) :=
  (F n) ⧸ associatedGradedModuleLower F F_lt n

/-- The additive direct sum of the associated graded module components. -/
abbrev associatedGradedModule (F F_lt : ℕ → Submodule R M) :=
  ⨁ n, associatedGradedModuleComponent F F_lt n

/-- The canonical map from a filtration term to its associated graded component. -/
abbrev associatedGradedModuleMk (F F_lt : ℕ → Submodule R M) (n : ℕ) :
    F n →ₗ[R] associatedGradedModuleComponent F F_lt n :=
  (associatedGradedModuleLower F F_lt n).mkQ

/-- A filtered-module carrier with its lower-term stability condition.

Mathlib supplies `IsModuleFiltration`; this condition supplies the quotient
descent needed for the associated graded scalar action.
-/
class IsAssociatedGradedModuleFiltration
    (A A_lt : ℕ → Submodule ℤ R) (F F_lt : ℕ → Submodule R M)
    [IsRingFiltration A A_lt] [IsModuleFiltration A A_lt F F_lt] : Prop where
  lower_smul_left : ∀ {i j : ℕ} {a : R}, a ∈ A_lt i →
    ∀ {m : M}, m ∈ F j → a • m ∈ F_lt (i + j)
  lower_smul_right : ∀ {i j : ℕ} {a : R}, a ∈ A i →
    ∀ {m : M}, m ∈ F_lt j → a • m ∈ F_lt (i + j)

private noncomputable def filteredModuleSmul
    (A : ℕ → Submodule ℤ R) (F : ℕ → Submodule R M) (i j : ℕ) :
    A i →ₗ[ℤ] F j →ₗ[R] F (i + j) :=
  LinearMap.mk₂' ℤ R
    (fun a m =>
      (⟨(a : R) • (m : M), SetLike.GradedSMul.smul_mem a.2 m.2⟩ : F (i + j)))
    (fun a₁ a₂ m => by ext; simp [add_smul])
    (fun c a m => by ext; simp [smul_assoc])
    (fun a m₁ m₂ => by ext; simp [smul_add])
    (fun c a m => by ext; simp [smul_comm])

/-- Scalar multiplication of homogeneous associated-graded module components. -/
noncomputable def associatedGradedModuleSmul
    (A A_lt : ℕ → Submodule ℤ R) (F F_lt : ℕ → Submodule R M)
    [IsRingFiltration A A_lt] [IsModuleFiltration A A_lt F F_lt]
    [IsAssociatedGradedModuleFiltration A A_lt F F_lt] (i j : ℕ) :
    (A i ⧸ (A_lt i).comap (A i).subtype) →ₗ[ℤ]
      associatedGradedModuleComponent F F_lt j →ₗ[R]
        associatedGradedModuleComponent F F_lt (i + j) := by
  apply LinearMap.liftQ₂
    ((A_lt i).comap (A i).subtype)
    (associatedGradedModuleLower F F_lt j)
    (filteredModuleSmul A F i j)
  · intro a ha
    apply LinearMap.ext
    intro m
    apply (Submodule.Quotient.mk_eq_zero).2
    exact IsAssociatedGradedModuleFiltration.lower_smul_left ha m.2
  · intro m hm
    apply LinearMap.ext
    intro a
    apply (Submodule.Quotient.mk_eq_zero).2
    exact IsAssociatedGradedModuleFiltration.lower_smul_right a.2 hm

@[simp]
theorem associatedGradedModuleSmul_mk (A A_lt : ℕ → Submodule ℤ R)
    (F F_lt : ℕ → Submodule R M)
    [IsRingFiltration A A_lt] [IsModuleFiltration A A_lt F F_lt]
    [IsAssociatedGradedModuleFiltration A A_lt F F_lt] (i j : ℕ)
    (a : A i) (m : F j) :
    associatedGradedModuleSmul A A_lt F F_lt i j
        ((A_lt i).comap (A i).subtype).mkQ a
        (associatedGradedModuleMk F F_lt j m) =
      associatedGradedModuleMk F F_lt (i + j) (filteredModuleSmul A F i j a m) :=
  rfl

end Module

end LeanCategories.Algebra
