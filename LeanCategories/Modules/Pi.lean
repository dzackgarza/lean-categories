/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Pi

@[expose] public section

universe u

namespace LinearEquiv

variable {ι : Type u} [DecidableEq ι]
variable (A : ι → Type u) [∀ i, CommRing (A i)]
variable (M N : ι → Type u)
variable [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
variable [∀ i, Module (A i) (M i)] [∀ i, Module (A i) (N i)]

private theorem piRing_single_supported
    (f : (∀ i, M i) ≃ₗ[(∀ i, A i)] ∀ i, N i)
    (i j : ι) (hji : j ≠ i) (x : M i) :
    f (Pi.single i x) j = 0 := by
  let a : ∀ i, A i := Pi.single i 1
  have hx : (Pi.single i x : ∀ i, M i) = a • Pi.single i x := by
    rw [← Pi.single_smul₀ i 1 x, one_smul]
  have hf : f (Pi.single i x) = a • f (Pi.single i x) := by
    calc
      f (Pi.single i x) = f (a • Pi.single i x) := congrArg f hx
      _ = a • f (Pi.single i x) := map_smul f a _
  have hj := congrArg (fun z ↦ z j) hf
  have ha : a j = 0 := by simp [a, hji]
  change f (Pi.single i x) j = a j • f (Pi.single i x) j at hj
  rw [ha, zero_smul] at hj
  exact hj

private theorem piRing_single_projection
    (f : (∀ i, M i) ≃ₗ[(∀ i, A i)] ∀ i, N i)
    (i : ι) (x : M i) :
    Pi.single i (f (Pi.single i x) i) = f (Pi.single i x) := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hji]
    exact (piRing_single_supported A M N f i j hji x).symm

/-- A linear equivalence over a product ring restricts to each coordinate module. -/
def piRingCoordinate
    (f : (∀ i, M i) ≃ₗ[(∀ i, A i)] ∀ i, N i) (i : ι) :
    M i ≃ₗ[A i] N i where
  toFun x := f (Pi.single i x) i
  invFun y := f.symm (Pi.single i y) i
  map_add' x y := by
    change f ((AddMonoidHom.single M i) (x + y)) i = _
    rw [map_add, map_add]
    rfl
  map_smul' r x := by
    rw [Pi.single_smul₀, map_smul]
    change (Pi.single i r : ∀ i, A i) i • f (Pi.single i x) i = _
    rw [Pi.single_eq_same]
    rfl
  left_inv x := by
    have hs := piRing_single_projection A M N f i x
    have h := congrArg (fun z ↦ z i) (f.symm_apply_apply (Pi.single i x))
    rw [← hs] at h
    rw [Pi.single_eq_same] at h
    exact h
  right_inv y := by
    have hs := piRing_single_projection A N M f.symm i y
    have h := congrArg (fun z ↦ z i) (f.apply_symm_apply (Pi.single i y))
    rw [← hs] at h
    rw [Pi.single_eq_same] at h
    exact h

end LinearEquiv
