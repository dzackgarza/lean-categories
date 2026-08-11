/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Ring.Basic

/-! # The inverse-limit topology on adic completions -/

@[expose] public section

noncomputable section

namespace AdicCompletion

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- Each quotient in the adic inverse system has its discrete topology. -/
@[reducible] def quotientPowTopology (n : ℕ) :
    TopologicalSpace (R ⧸ I ^ n) :=
  ⊥

/-- The inclusion of the compatible families into the product of quotient rings. -/
def valRingHom : AdicCompletion I R →+*
    ((n : ℕ) → R ⧸ I ^ n) where
  toFun x n := AdicCompletion.evalₐ I n x
  map_one' := by funext n; simp
  map_mul' _ _ := by funext n; simp
  map_zero' := by funext n; simp
  map_add' _ _ := by funext n; simp

/-- The adic completion has the subspace topology from the product of discrete quotients. -/
instance adicCompletionTopologicalSpace : TopologicalSpace (AdicCompletion I R) := by
  letI (n : ℕ) : TopologicalSpace (R ⧸ I ^ n) :=
    quotientPowTopology R I n
  exact TopologicalSpace.induced (valRingHom R I)
    inferInstance

/-- The adic completion is a topological ring for its inverse-limit topology. -/
instance : IsTopologicalRing (AdicCompletion I R) := by
  letI (n : ℕ) : TopologicalSpace (R ⧸ I ^ n) :=
    quotientPowTopology R I n
  letI (n : ℕ) : DiscreteTopology (R ⧸ I ^ n) :=
    ⟨rfl⟩
  letI : IsTopologicalRing
      ((n : ℕ) → R ⧸ I ^ n) :=
    inferInstance
  exact
    { ContinuousAdd.induced (valRingHom R I),
      ContinuousMul.induced (valRingHom R I),
      ContinuousNeg.induced (valRingHom R I) with }

/-- Every quotient projection from the adic inverse limit is continuous. -/
theorem continuous_eval (n : ℕ) :
    @Continuous (AdicCompletion I R)
      (R ⧸ I ^ n) inferInstance
      (quotientPowTopology R I n) (AdicCompletion.evalₐ I n) := by
  letI (m : ℕ) : TopologicalSpace (R ⧸ I ^ m) :=
    quotientPowTopology R I m
  have hval : Continuous (valRingHom R I) := continuous_induced_dom
  exact (continuous_apply n).comp hval

end AdicCompletion

namespace IsAdic

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Quotient maps to the discrete finite-level rings are continuous for an adic topology. -/
theorem continuous_quotient_mk {I : Ideal A} (hI : IsAdic I) (n : ℕ) :
    @Continuous A (A ⧸ I ^ n) inferInstance ⊥ (Ideal.Quotient.mk (I ^ n)) := by
  letI : TopologicalSpace (A ⧸ I ^ n) := ⊥
  letI : DiscreteTopology (A ⧸ I ^ n) := ⟨rfl⟩
  apply continuous_of_tendsto_nhds_zero (Ideal.Quotient.mk (I ^ n))
  rw [show @nhds (A ⧸ I ^ n) ⊥ 0 = pure 0 by simp]
  rw [Filter.tendsto_pure]
  exact hI.hasBasis_nhds_zero.mem_iff.mpr
    ⟨n, trivial, fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr hx⟩

end IsAdic
