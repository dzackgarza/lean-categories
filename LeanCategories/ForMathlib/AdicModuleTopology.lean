/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Adic topologies on modules

Atiyah–Macdonald (1969), printed p. 105, FC04-C10-U019. The powers `IⁿM`
form the zero-neighborhood basis. Linear maps and the discrete quotient maps are
continuous for this topology. These facts belong to the original modules, before
forming their completions or comparing other filtrations.
-/

@[expose] public section

open Topology

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The powers of the ideal acting on the module form its adic zero-neighborhood basis. -/
theorem hasBasis_nhds_zero_adicModule :
    Filter.HasBasis (@nhds M (I.adicModuleTopology M) 0) (fun _ : ℕ => True)
      (fun n => (↑(I ^ n • ⊤ : Submodule R M) : Set M)) := by
  let : TopologicalSpace R := I.adicTopology
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  refine ⟨fun s => ?_⟩
  rw [B.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
  constructor
  · rintro ⟨U, ⟨n, rfl⟩, hU⟩
    exact ⟨n, trivial, hU⟩
  · rintro ⟨n, _, hU⟩
    exact ⟨_, ⟨n, rfl⟩, hU⟩

variable {M} {N : Type*} [AddCommGroup N] [Module R N]

/-- Every linear map is continuous for the adic topologies on its source and target. -/
theorem continuous_linearMap_adic (f : M →ₗ[R] N) :
    @Continuous M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := I.adicModuleTopology N
  apply continuous_of_tendsto_nhds_zero f
  apply (I.hasBasis_nhds_zero_adicModule M).tendsto_iff
    (I.hasBasis_nhds_zero_adicModule N) |>.mpr
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro m hm
  exact (show Submodule.map f (I ^ n • ⊤) ≤ (I ^ n • ⊤ : Submodule R N) by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top) (Submodule.mem_map.mpr ⟨m, hm, rfl⟩)

variable (M)

/-- Quotient maps to the discrete finite-level modules are continuous in the adic topology. -/
theorem continuous_quotient_mk_adicModule (n : ℕ) :
    @Continuous M (M ⧸ (I ^ n • ⊤ : Submodule R M)) (I.adicModuleTopology M) ⊥
      (Submodule.mkQ (I ^ n • ⊤)) := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  let : DiscreteTopology (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⟨rfl⟩
  apply continuous_of_tendsto_nhds_zero (Submodule.mkQ (I ^ n • ⊤ : Submodule R M))
  rw [show @nhds (M ⧸ (I ^ n • ⊤ : Submodule R M)) ⊥ 0 = pure 0 by simp,
    Filter.tendsto_pure]
  exact (I.hasBasis_nhds_zero_adicModule M).mem_iff.mpr
    ⟨n, trivial, fun x hx => (Submodule.Quotient.mk_eq_zero _).mpr hx⟩

end Ideal
