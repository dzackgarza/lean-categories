/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.AdicCompletionTopology
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Adic completion as uniform completion

Atiyah–Macdonald (1969), printed pp. 103–105, FC04-C10-U018–U019.
The inverse limit of the discrete quotients is complete, and the original module
maps densely into it with its original adic uniformity. Mathlib's universal comparison
of completions gives a topological additive isomorphism, compatible with the original map.

No separation assumption on the original module and no finite-generation assumption
on the ideal is imposed. Completeness refers to the residue inverse-limit uniformity,
not to an unproved identification with powers of the extended ideal.
-/

@[expose] public section

open Topology Filter

noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The subspace uniformity from the product of discrete module quotients. -/
instance adicCompletionUniformSpace : UniformSpace (AdicCompletion I M) := by
  let (n : ℕ) : UniformSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  exact UniformSpace.comap Subtype.val inferInstance

-- The additional uniform structure does not introduce a second topology.
example : (adicCompletionUniformSpace I M).toTopologicalSpace =
    adicCompletionTopologicalSpace R I M := rfl

/-- Addition and subtraction are uniformly continuous in the inverse-limit uniformity. -/
instance : IsUniformAddGroup (AdicCompletion I M) := by
  let (n : ℕ) : UniformSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  exact IsUniformAddGroup.comap (submodule I M).subtype.toAddMonoidHom

/-- Compatible residue families form a closed subspace of a complete product. -/
instance : CompleteSpace (AdicCompletion I M) := by
  let (n : ℕ) : UniformSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  have hc : IsClosed ((submodule I M) : Set ((n : ℕ) → M ⧸ (I ^ n • ⊤ : Submodule R M))) := by
    change IsClosed {x : (n : ℕ) → M ⧸ (I ^ n • ⊤ : Submodule R M) |
      ∀ (m n : ℕ) (h : m ≤ n), transitionMap I M h (x n) = x m}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro m
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro h
    exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n))
      (continuous_apply m)
  exact hc.completeSpace_coe

/-- The canonical map induces the original adic topology, without requiring injectivity. -/
theorem isInducing_of :
    @Topology.IsInducing M (AdicCompletion I M) (I.adicModuleTopology M) inferInstance
      (of I M) := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  have ht : @IsTopologicalAddGroup M (TopologicalSpace.induced (of I M) inferInstance) _ := by
    let : TopologicalSpace M := TopologicalSpace.induced (of I M) inferInstance
    exact { ContinuousAdd.induced (of I M), ContinuousNeg.induced (of I M) with }
  refine ⟨?_⟩
  apply IsTopologicalAddGroup.ext (inferInstance : IsTopologicalAddGroup M) ht
  rw [nhds_induced, _root_.map_zero]
  apply le_antisymm
  · rw [← Filter.tendsto_iff_comap]
    simpa only [ContinuousAt, _root_.map_zero] using (continuous_of I M).continuousAt (x := 0)
  · apply (I.hasBasis_nhds_zero_adicModule M).ge_iff.mpr
    intro n _
    let : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
    let : DiscreteTopology (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⟨rfl⟩
    have ho : IsOpen {x : AdicCompletion I M | eval I M n x = 0} :=
      (isOpen_discrete {0}).preimage (continuous_eval_module R I M n)
    refine Filter.mem_comap.mpr ⟨_, ho.mem_nhds (_root_.map_zero (eval I M n)), ?_⟩
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).mp hx

/-- The residue inverse limit is a complete separated uniform completion of the module. -/
def abstractCompletion :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace M := I.adicModuleTopology M
    letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    AbstractCompletion M := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  exact {
    space := AdicCompletion I M
    coe := of I M
    uniformStruct := inferInstance
    complete := inferInstance
    separation := inferInstance
    isUniformInducing := AddMonoidHom.isUniformInducing_of_isInducing
      (f := (of I M).toAddMonoidHom) (isInducing_of I M)
    dense := denseRange_of I M }

/-- The canonical topological additive isomorphism from uniform completion to adic completion. -/
def completionAddEquiv :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace M := I.adicModuleTopology M
    letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    letI : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
    UniformSpace.Completion M ≃ₜ+ AdicCompletion I M := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  let e : UniformSpace.Completion M ≃ᵤ AdicCompletion I M :=
    (UniformSpace.Completion.cPkg (α := M)).compareEquiv (abstractCompletion I M)
  exact { e.toHomeomorph with
    map_add' := ((of I M).toAddMonoidHom.extension (continuous_of I M)).map_add }

/-- The completion comparison extends the original module's canonical map. -/
theorem completionAddEquiv_coe (m : M) :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace M := I.adicModuleTopology M
    letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    letI : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
    completionAddEquiv I M (m : UniformSpace.Completion M) = of I M m := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  exact (UniformSpace.Completion.cPkg (α := M)).compare_coe (abstractCompletion I M) m

end AdicCompletion
