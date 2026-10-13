/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Serre's degree-one homology convention

Definition-level realization of Serre, *Local Fields*, Chapter VII,
`FC10-C07-U021`.

Pinned Mathlib identifies the first homology of a trivial representation with
the tensor product of the abelianization and the coefficient module.  For
integral trivial coefficients, the tensor right-unitor gives Serre's displayed
identification `H₁(G, ℤ) ≃ G/G'` directly.

The comparison with the separate augmentation-ideal presentation
`I_G / I_G²` is a theorem about this equivalence and is not part of the Sweep-III
declaration.
-/

@[expose] public noncomputable section

open Rep TensorProduct

namespace LeanCategories.Homological

variable (G : Type) [Group G]

/-- Serre's convention identifying `H₁(G, ℤ)` with the additive form of the
abelianization `G/G'` (FC10-C07-U021). -/
noncomputable def serreH1AbelianizationEquiv :
    groupHomology (Rep.trivial ℤ G ℤ) 1 ≃+ Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

end LeanCategories.Homological
