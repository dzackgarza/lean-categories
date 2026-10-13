/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Universal Casimir source data

Humphreys FC14-C06-U026. Once Killing-dual Cartan bases and dual root
vectors have been chosen, the universal Casimir is the displayed finite sum
of products in the universal enveloping algebra. Centrality and representation
action are theorem content.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Algebra

universe u v w x

variable (K : Type u) (L : Type v)
variable [CommRing K] [LieRing L] [LieAlgebra K L]

/-- The Humphreys Casimir formula after the dual Cartan/root families have
already been chosen. The hypotheses making the supplied families Killing-dual
belong to the source setup, not to this finite-sum operation. -/
def casimirElementFromDualFamilies
    {I : Type w} {Phi : Type x} [Fintype I] [Fintype Phi]
    (h k : I → L) (x z : Phi → L) : UniversalEnvelopingAlgebra K L :=
  ∑ i, UniversalEnvelopingAlgebra.ι K (h i) * UniversalEnvelopingAlgebra.ι K (k i) +
    ∑ alpha, UniversalEnvelopingAlgebra.ι K (x alpha) *
      UniversalEnvelopingAlgebra.ι K (z alpha)

end LeanCategories.Algebra
