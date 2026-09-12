/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Ring.Defs

/-!
# Steinberg groups

Weibel, *An Introduction to Homological Algebra* (1994), Definition 6.9.13,
pp. 198--202 (FC05-C06-U120).

For `n ≥ 3`, `Stₙ(R)` is presented by generators `xᵢⱼ(a)` (`i ≠ j`) and
the additive and Steinberg commutator relations.  The natural map to the
elementary matrix group is result-level content.
-/

@[expose] public section

namespace LeanCategories.Homological

open scoped commutatorElement

universe u

/-- A formal Steinberg generator `xᵢⱼ(a)`. -/
structure SteinbergGenerator (n : ℕ) (R : Type u) where
  i : Fin n
  j : Fin n
  hij : i ≠ j
  value : R

namespace SteinbergGenerator

variable {n : ℕ} {R : Type u}

/-- The free-group generator attached to `xᵢⱼ(a)`. -/
def free (x : SteinbergGenerator n R) : FreeGroup (SteinbergGenerator n R) :=
  FreeGroup.of x

end SteinbergGenerator

/-- Additive relator `xᵢⱼ(a)xᵢⱼ(b)=xᵢⱼ(a+b)`. -/
def steinbergAddRelator (n : ℕ) (R : Type u) [Ring R]
    (i j : Fin n) (hij : i ≠ j) (a b : R) :
    FreeGroup (SteinbergGenerator n R) :=
  SteinbergGenerator.free ⟨i, j, hij, a⟩ *
    SteinbergGenerator.free ⟨i, j, hij, b⟩ *
    (SteinbergGenerator.free ⟨i, j, hij, a + b⟩)⁻¹

/-- Distant-root relator `[xᵢⱼ(a),xₖₗ(b)]=1` when `i≠l` and `j≠k`. -/
def steinbergFarCommRelator
    (n : ℕ) (R : Type u) [Ring R]
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (_hil : i ≠ l) (_hjk : j ≠ k) (a b : R) :
    FreeGroup (SteinbergGenerator n R) :=
  ⁅SteinbergGenerator.free ⟨i, j, hij, a⟩,
    SteinbergGenerator.free ⟨k, l, hkl, b⟩⁆

/-- Steinberg relator `[xᵢⱼ(a),xⱼₖ(b)]=xᵢₖ(ab)` for pairwise distinct `i,j,k`. -/
def steinbergChainRelator
    (n : ℕ) (R : Type u) [Ring R]
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) : FreeGroup (SteinbergGenerator n R) :=
  ⁅SteinbergGenerator.free ⟨i, j, hij, a⟩,
    SteinbergGenerator.free ⟨j, k, hjk, b⟩⁆ *
    (SteinbergGenerator.free ⟨i, k, hik, a * b⟩)⁻¹

/-- The set of defining relators for `Stₙ(R)`. -/
def steinbergRelators (n : ℕ) (R : Type u) [Ring R] :
    Set (FreeGroup (SteinbergGenerator n R)) :=
  {r | (∃ i j hij a b, r = steinbergAddRelator n R i j hij a b) ∨
    (∃ i j k l hij hkl hil hjk a b,
      r = steinbergFarCommRelator n R i j k l hij hkl hil hjk a b) ∨
    (∃ i j k hij hjk hik a b,
      r = steinbergChainRelator n R i j k hij hjk hik a b)}

/-- The Steinberg group `Stₙ(R)` for source rank `n ≥ 3`. -/
abbrev SteinbergGroup (n : ℕ) (R : Type u) [Ring R] (_hn : 3 ≤ n) : Type u :=
  PresentedGroup (steinbergRelators n R)

end LeanCategories.Homological
