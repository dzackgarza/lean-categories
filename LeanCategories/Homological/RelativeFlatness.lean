/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.KSplitComplex
public import LeanCategories.Homological.NoncommutativeTensor
public import Mathlib.Algebra.Homology.Additive

/-!
# Relative flatness over a base ring

Weibel, *An Introduction to Homological Algebra* (1994), §8.7, pp. 286--293
(FC05-C08-U092).

A right `R`-module `P` is relatively flat over `R/k` when tensoring with `P`
sends every `k`-split exact complex of left `R`-modules to an exact complex.
The equivalent characterization by vanishing of relative Tor is result-level
content and is not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u v w

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]

/-- Tensor a chain complex of left `R`-modules with a fixed right `R`-module. -/
noncomputable def tensorRightModuleChainComplex
    (P : ModuleCat.{w} Rᵐᵒᵖ)
    (N : ChainComplex (ModuleCat.{w} R) ℕ) : ChainComplex (ModuleCat.{w} ℤ) ℕ :=
  (((tensorLeftFunctor R P).mapHomologicalComplex (ComplexShape.down ℕ)).obj N)

/-- Weibel's relative flatness condition over `R/k`. -/
def IsRelativelyFlatRightModule (P : ModuleCat.{w} Rᵐᵒᵖ) : Prop :=
  ∀ N : ChainComplex (ModuleCat.{w} R) ℕ,
    IsKSplitComplex k R N →
      (tensorRightModuleChainComplex R P N).Acyclic

end LeanCategories.Homological
