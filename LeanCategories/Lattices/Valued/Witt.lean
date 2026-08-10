/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Constructions
public import LeanCategories.Modules.Bilinear.Valued.Witt

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K]

/-- The finite hyperbolic symmetric form on `Mᵛ × M`. -/
noncomputable def hyperbolicFiniteForm
    (M : Type u) [AddCommGroup M] [Module K M] [Module.Finite K M] :
    FiniteFormCat K K := by
  refine ⟨hyperbolicBilinModule K M, ?_, ?_⟩
  · change Module.Finite K (Module.Dual K M × M)
    infer_instance
  · exact (LinearMap.isSymm_dualProd (R := K) (M := M)).eq

/-- A chosen hyperbolic summand and its orthogonal complement. -/
structure HyperbolicSummand (L : FiniteFormCat K K) where
  carrier : Type u
  [carrierAddCommGroup : AddCommGroup carrier]
  [carrierModule : Module K carrier]
  [carrierFinite : Module.Finite K carrier]
  complement : FiniteFormCat K K
  decomposition :
    L ≅ finiteFormOrthogonalSum complement (hyperbolicFiniteForm K carrier)

/-- A Witt decomposition has an anisotropic complement. -/
structure WittDecomposition (L : FiniteFormCat K K)
    extends HyperbolicSummand K L where
  complement_isAnisotropic : complement.obj.IsAnisotropic

/-- A finite form has a hyperbolic summand when such decomposition data exists. -/
def HasHyperbolicSummand (L : FiniteFormCat K K) : Prop :=
  Nonempty (HyperbolicSummand K L)

/-- A finite form has a Witt decomposition when such decomposition data exists. -/
def HasWittDecomposition (L : FiniteFormCat K K) : Prop :=
  Nonempty (WittDecomposition K L)

/-- An isometry after adding finite hyperbolic forms to both sides. -/
structure WittStableIsometry (L M : FiniteFormCat K K) where
  leftCarrier : Type u
  [leftCarrierAddCommGroup : AddCommGroup leftCarrier]
  [leftCarrierModule : Module K leftCarrier]
  [leftCarrierFinite : Module.Finite K leftCarrier]
  rightCarrier : Type u
  [rightCarrierAddCommGroup : AddCommGroup rightCarrier]
  [rightCarrierModule : Module K rightCarrier]
  [rightCarrierFinite : Module.Finite K rightCarrier]
  isometry :
    finiteFormOrthogonalSum L (hyperbolicFiniteForm K leftCarrier) ≅
      finiteFormOrthogonalSum M (hyperbolicFiniteForm K rightCarrier)

/-- Two finite forms are Witt equivalent when they are stably isometric. -/
def IsWittEquivalent (L M : FiniteFormCat K K) : Prop :=
  Nonempty (WittStableIsometry K L M)

/-- A Witt decomposition gives a hyperbolic summand. -/
theorem HasWittDecomposition.hasHyperbolicSummand
    {L : FiniteFormCat K K} (hL : HasWittDecomposition K L) :
    HasHyperbolicSummand K L :=
  hL.map WittDecomposition.toHyperbolicSummand

end LeanCategories.Lattices.Valued
