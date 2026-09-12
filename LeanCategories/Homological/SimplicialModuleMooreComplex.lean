/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Normalized Moore complex of a simplicial module

Weibel, *An Introduction to Homological Algebra* (1994), §8.3, pp. 263--269
(FC05-C08-U030).

Pinned Mathlib's `normalizedMooreComplex` is exactly the source construction:
in degree `n` it is the intersection of the kernels of the first `n` face
maps, and its differential is induced by the remaining face.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Simplicial

universe u v

variable (R : Type u) [Ring R]

/-- Weibel's normalized Moore complex of a simplicial `R`-module. -/
noncomputable def simplicialModuleMooreComplex
    (A : SimplicialObject (ModuleCat.{v} R)) : ChainComplex (ModuleCat.{v} R) ℕ :=
  (AlgebraicTopology.normalizedMooreComplex (ModuleCat.{v} R)).obj A

/-- The degree-`n` normalized Moore object, exposing Mathlib's exact
intersection-of-kernels owner. -/
noncomputable abbrev simplicialModuleMooreDegree
    (A : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) : ModuleCat.{v} R :=
  (simplicialModuleMooreComplex R A).X n

end LeanCategories.Homological
