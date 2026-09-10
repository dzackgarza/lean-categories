/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.AddSubgroupTopology
public import LeanCategories.ForMathlib.AdicModuleTopology
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Int

/-!
# Topologies of stable module filtrations

Atiyah–Macdonald (1969), printed pp. 105–106, FC04-C10-U022–U023.
Mathlib's `Ideal.Filtration` allows any initial submodule; the source additionally
requires `F.N 0 = ⊤`. The bounded-difference theorem is reused to identify topologies
when the initial terms agree. For the source-normalized filtrations the resulting
topology is exactly the adic topology of the whole module.
-/

@[expose] public section

open Topology Filter

namespace Ideal.Filtration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Ideal R}

/-- The subgroup topology of a module filtration. -/
@[instance_reducible]
def topology (F : I.Filtration M) : TopologicalSpace M :=
  AddSubgroup.topologyOfAntitone (fun n => (F.N n).toAddSubgroup)
    (fun _ _ h => F.antitone h)

/-- Stable filtrations with the same initial term induce the same topology. -/
theorem Stable.topology_eq {F F' : I.Filtration M} (h : F.Stable) (h' : F'.Stable)
    (e : F.N 0 = F'.N 0) : F.topology = F'.topology := by
  obtain ⟨k, hk⟩ := h.bounded_difference h' e
  apply (AddSubgroup.topologyOfAntitone_eq_iff _ _ _ _).mpr
  exact ⟨fun n => ⟨n + k, (hk n).1⟩, fun n => ⟨n + k, (hk n).2⟩⟩

/-- The power filtration of the whole module gives its adic topology. -/
theorem topology_stableFiltration_top (I : Ideal R) :
    (I.stableFiltration (⊤ : Submodule R M)).topology = I.adicModuleTopology M := by
  let : TopologicalSpace R := I.adicTopology
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  apply IsTopologicalAddGroup.ext
    (AddSubgroup.filterBasisOfAntitone
      (fun n => ((I.stableFiltration (⊤ : Submodule R M)).N n).toAddSubgroup)
      (fun _ _ h => (I.stableFiltration (⊤ : Submodule R M)).antitone h)).isTopologicalAddGroup
    B.toAddGroupFilterBasis.isTopologicalAddGroup
  apply Filter.ext
  intro s
  have b := AddSubgroup.hasBasis_nhds_zero_topologyOfAntitone
    (fun n => ((I.stableFiltration (⊤ : Submodule R M)).N n).toAddSubgroup)
    (fun _ _ h => (I.stableFiltration (⊤ : Submodule R M)).antitone h)
  rw [b.mem_iff, (I.hasBasis_nhds_zero_adicModule M).mem_iff]
  rfl

/-- Every stable filtration starting with the whole module gives the adic topology. -/
theorem Stable.topology_eq_adic {F : I.Filtration M} (h : F.Stable)
    (h0 : F.N 0 = ⊤) : F.topology = I.adicModuleTopology M := by
  calc
    F.topology = (I.stableFiltration (⊤ : Submodule R M)).topology :=
      h.topology_eq (I.stableFiltration_stable ⊤) (by simpa using h0)
    _ = I.adicModuleTopology M := topology_stableFiltration_top I

example (I : Ideal ℤ) : (I.stableFiltration (⊤ : Submodule ℤ (Fin 2 → ℤ))).topology =
    I.adicModuleTopology (Fin 2 → ℤ) := topology_stableFiltration_top I

-- Stability alone does not impose the source normalization of the initial term.
example : ((⊤ : Ideal ℤ).trivialFiltration (⊥ : Submodule ℤ ℤ)).Stable := by
  use 0
  intro n _
  simp [Ideal.trivialFiltration]

example : ((⊤ : Ideal ℤ).trivialFiltration (⊥ : Submodule ℤ ℤ)).N 0 ≠ ⊤ := by
  change (⊥ : Submodule ℤ ℤ) ≠ ⊤
  exact bot_ne_top

example : ((⊤ : Ideal ℤ).trivialFiltration (⊥ : Submodule ℤ ℤ)).topology ≠
    ((⊤ : Ideal ℤ).trivialFiltration (⊤ : Submodule ℤ ℤ)).topology := by
  intro h
  obtain ⟨m, hm⟩ := ((AddSubgroup.topologyOfAntitone_eq_iff _ _ _ _).mp h).2 0
  have hz := hm (show (1 : ℤ) ∈ ((⊤ : Ideal ℤ).trivialFiltration (⊤ : Submodule ℤ ℤ)).N m
    from Submodule.mem_top)
  change (1 : ℤ) ∈ (⊥ : Submodule ℤ ℤ) at hz
  norm_num at hz

end Ideal.Filtration

-- The source's subgroup sequence pⁿℤ is the principal-ideal power filtration.
example (p : ℤ) (n : ℕ) :
    (((Ideal.span ({p} : Set ℤ)).stableFiltration (⊤ : Submodule ℤ ℤ)).N n).toAddSubgroup =
      AddSubgroup.zmultiples (p ^ n) := by
  change (((Ideal.span ({p} : Set ℤ)) ^ n) • (⊤ : Ideal ℤ)).toAddSubgroup = _
  simp [Ideal.span_singleton_pow, Ideal.span_singleton_toAddSubgroup_eq_zmultiples]
