/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.AddSubgroupTopology
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Completion from a descending family of additive subgroups

Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), printed pp. 102–104,
FC04-C10-U007–U008. A descending subgroup family defines quotient transition maps;
its inverse limit is the additive group of coherent residue classes. With the subgroup-basis
topology on the original group and the product-subspace topology on coherent residues, the
diagonal map is dense and uniform-inducing, so this inverse limit is canonically the usual
Hausdorff completion.

The construction is independent of adic module structure. It therefore sits at the additive-group
owner and specializes later to ideal-power completions.
-/

@[expose] public section

open Topology Filter

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G]
variable (F : ℕ → AddSubgroup G) (hF : Antitone F)

/-- Transition map in the quotient inverse system associated to a descending subgroup family. -/
def quotientTransition {m n : ℕ} (h : m ≤ n) : G ⧸ F n →+ G ⧸ F m :=
  QuotientAddGroup.map (F n) (F m) (AddMonoidHom.id G) (by
    intro x hx
    change x ∈ F m
    exact hF h hx)

@[simp] theorem quotientTransition_mk {m n : ℕ} (h : m ≤ n) (x : G) :
    quotientTransition F hF h (QuotientAddGroup.mk x) = QuotientAddGroup.mk x := rfl

/-- The coherent residue families form an additive subgroup of the product of quotients. -/
def completionSubgroup : AddSubgroup (∀ n : ℕ, G ⧸ F n) where
  carrier := {x | ∀ {m n} (h : m ≤ n), quotientTransition F hF h (x n) = x m}
  zero_mem' := by intro m n h; simp [quotientTransition]
  add_mem' hx hy := by
    intro m n h
    simp only [Pi.add_apply, map_add, hx h, hy h]
  neg_mem' hx := by
    intro m n h
    simp only [Pi.neg_apply, map_neg, hx h]

/-- Coherent residue families for the quotients by a descending subgroup family. -/
abbrev Completion : Type _ := completionSubgroup F hF

/-- Projection to a finite quotient. -/
def Completion.eval (n : ℕ) : Completion F hF →+ G ⧸ F n :=
  AddMonoidHom.comp (Pi.evalAddMonoidHom (fun n : ℕ => G ⧸ F n) n)
    (completionSubgroup F hF).subtype

/-- The diagonal map into coherent residues. -/
def Completion.of : G →+ Completion F hF where
  toFun x := ⟨fun n => QuotientAddGroup.mk x, by intro m n h; rfl⟩
  map_zero' := by apply Subtype.ext; funext n; rfl
  map_add' x y := by apply Subtype.ext; funext n; rfl

@[simp] theorem Completion.eval_of (n : ℕ) (x : G) :
    Completion.eval F hF n (Completion.of F hF x) = QuotientAddGroup.mk x := rfl



/-- The quotient maps form the inverse system underlying the coherent completion. -/
instance quotientInverseSystem :
    InverseSystem (fun {_ _ : ℕ} h => quotientTransition F hF h) where
  map_self {i} x := by
    induction x using Quotient.inductionOn'
    rfl
  map_map {k j i} hkj hji x := by
    induction x using Quotient.inductionOn'
    rfl


namespace Completion

/-- The coherent-residue completion has the subspace topology from the product of
discrete quotients. -/
instance topologicalSpace : TopologicalSpace (Completion F hF) := by
  let (n : ℕ) : TopologicalSpace (G ⧸ F n) := ⊥
  exact TopologicalSpace.induced Subtype.val inferInstance

/-- Continuity into the coherent completion is coordinatewise continuity. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → Completion F hF) :
    Continuous f ↔ ∀ n : ℕ, @Continuous X (G ⧸ F n) inferInstance ⊥
      (fun x => eval F hF n (f x)) := by
  let (n : ℕ) : TopologicalSpace (G ⧸ F n) := ⊥
  constructor
  · intro h n
    exact (continuous_apply n).comp (continuous_induced_rng.mp h)
  · intro h
    exact continuous_induced_rng.mpr (continuous_pi h)

/-- Each coherent-residue projection is continuous. -/
theorem continuous_eval (n : ℕ) :
    @Continuous (Completion F hF) (G ⧸ F n) inferInstance ⊥ (eval F hF n) :=
  (continuous_iff F hF id).mp continuous_id n

instance : T2Space (Completion F hF) := by
  let (n : ℕ) : TopologicalSpace (G ⧸ F n) := ⊥
  let (n : ℕ) : DiscreteTopology (G ⧸ F n) := ⟨rfl⟩
  apply Topology.IsEmbedding.t2Space (f := (completionSubgroup F hF).subtype)
  exact ⟨⟨rfl⟩, Subtype.val_injective⟩

instance : IsTopologicalAddGroup (Completion F hF) := by
  let (n : ℕ) : TopologicalSpace (G ⧸ F n) := ⊥
  let (n : ℕ) : DiscreteTopology (G ⧸ F n) := ⟨rfl⟩
  exact { ContinuousAdd.induced (completionSubgroup F hF).subtype,
    ContinuousNeg.induced (completionSubgroup F hF).subtype with }

/-- The diagonal map is continuous for the subgroup-basis topology. -/
theorem continuous_of :
    @Continuous G (Completion F hF) (topologyOfAntitone F hF) inferInstance (of F hF) := by
  let : TopologicalSpace G := topologyOfAntitone F hF
  apply (continuous_iff F hF _).mpr
  intro n
  let : TopologicalSpace (G ⧸ F n) := ⊥
  let : DiscreteTopology (G ⧸ F n) := ⟨rfl⟩
  apply continuous_of_tendsto_nhds_zero (QuotientAddGroup.mk' (F n))
  rw [show @nhds (G ⧸ F n) ⊥ 0 = pure 0 by simp, Filter.tendsto_pure]
  exact (hasBasis_nhds_zero_topologyOfAntitone F hF).mem_iff.mpr
    ⟨n, trivial, fun x hx => QuotientAddGroup.eq_zero_iff x |>.mpr hx⟩

/-- Representatives of coherent residues converge to the corresponding completion point. -/
theorem tendsto_out (x : Completion F hF) :
    Filter.Tendsto (fun n => of F hF (x.1 n).out) Filter.atTop (nhds x) := by
  let (n : ℕ) : TopologicalSpace (G ⧸ F n) := ⊥
  let (n : ℕ) : DiscreteTopology (G ⧸ F n) := ⟨rfl⟩
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  rw [nhds_discrete, Filter.tendsto_pure]
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  change QuotientAddGroup.mk (x.1 n).out = x.1 k
  calc
    QuotientAddGroup.mk (x.1 n).out =
        quotientTransition F hF hn (QuotientAddGroup.mk (x.1 n).out) :=
      (quotientTransition_mk F hF hn _).symm
    _ = quotientTransition F hF hn (x.1 n) :=
      congrArg (quotientTransition F hF hn) (x.1 n).out_eq'
    _ = x.1 k := x.2 hn

/-- The original group is dense in its coherent-residue completion. -/
theorem denseRange_of : DenseRange (of F hF) := by
  intro x
  exact mem_closure_of_tendsto (tendsto_out F hF x)
    (Filter.Eventually.of_forall fun n => Set.mem_range_self (x.1 n).out)

end Completion


namespace Completion

/-- The product-subspace uniformity on coherent residues. -/
instance uniformSpace : UniformSpace (Completion F hF) := by
  let (n : ℕ) : UniformSpace (G ⧸ F n) := ⊥
  exact UniformSpace.comap Subtype.val inferInstance

example : (uniformSpace F hF).toTopologicalSpace = topologicalSpace F hF := rfl

instance : IsUniformAddGroup (Completion F hF) := by
  let (n : ℕ) : UniformSpace (G ⧸ F n) := ⊥
  exact IsUniformAddGroup.comap (completionSubgroup F hF).subtype

/-- Coherent residue families form a closed subspace of the complete product. -/
instance : CompleteSpace (Completion F hF) := by
  let (n : ℕ) : UniformSpace (G ⧸ F n) := ⊥
  have hc : IsClosed ((completionSubgroup F hF) : Set ((n : ℕ) → G ⧸ F n)) := by
    change IsClosed {x : (n : ℕ) → G ⧸ F n |
      ∀ (m n : ℕ) (h : m ≤ n), quotientTransition F hF h (x n) = x m}
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro m
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro h
    exact isClosed_eq
      ((continuous_of_discreteTopology (f := quotientTransition F hF h)).comp (continuous_apply n))
      (continuous_apply m)
  exact hc.completeSpace_coe

/-- The diagonal map induces exactly the subgroup-basis topology. -/
theorem isInducing_of :
    @Topology.IsInducing G (Completion F hF) (topologyOfAntitone F hF) inferInstance
      (of F hF) := by
  let : TopologicalSpace G := topologyOfAntitone F hF
  have ht : @IsTopologicalAddGroup G (TopologicalSpace.induced (of F hF) inferInstance) _ := by
    let : TopologicalSpace G := TopologicalSpace.induced (of F hF) inferInstance
    exact { ContinuousAdd.induced (of F hF), ContinuousNeg.induced (of F hF) with }
  refine ⟨?_⟩
  apply IsTopologicalAddGroup.ext
    (AddSubgroup.filterBasisOfAntitone F hF).isTopologicalAddGroup ht
  rw [nhds_induced, map_zero]
  apply le_antisymm
  · rw [← Filter.tendsto_iff_comap]
    simpa only [ContinuousAt, map_zero] using (continuous_of F hF).continuousAt (x := 0)
  · apply (hasBasis_nhds_zero_topologyOfAntitone F hF).ge_iff.mpr
    intro n _
    let : TopologicalSpace (G ⧸ F n) := ⊥
    let : DiscreteTopology (G ⧸ F n) := ⟨rfl⟩
    have ho : IsOpen {x : Completion F hF | eval F hF n x = 0} :=
      (isOpen_discrete {0}).preimage (continuous_eval F hF n)
    refine Filter.mem_comap.mpr ⟨_, ho.mem_nhds (map_zero (eval F hF n)), ?_⟩
    intro x hx
    exact (QuotientAddGroup.eq_zero_iff x).mp hx

/-- Representatives of a coherent residue family form a Cauchy sequence in the
original subgroup-basis topology. -/
theorem cauchySeq_out (x : Completion F hF) :
    letI : TopologicalSpace G := topologyOfAntitone F hF
    letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
    CauchySeq (fun n => (x.1 n).out) := by
  let : TopologicalSpace G := topologyOfAntitone F hF
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  let : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have hu : IsUniformInducing (of F hF) :=
    AddMonoidHom.isUniformInducing_of_isInducing (isInducing_of F hF)
  unfold CauchySeq
  rw [← hu.cauchy_map_iff]
  rw [Filter.map_map]
  exact (tendsto_out F hF x).cauchySeq

/-- Coherent residues give a complete separated uniform completion of the
subgroup-topological group. -/
def abstractCompletion :
    letI : TopologicalSpace G := topologyOfAntitone F hF
    letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
    AbstractCompletion G := by
  let : TopologicalSpace G := topologyOfAntitone F hF
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  let : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  exact {
    space := Completion F hF
    coe := of F hF
    uniformStruct := inferInstance
    complete := inferInstance
    separation := inferInstance
    isUniformInducing := AddMonoidHom.isUniformInducing_of_isInducing
      (f := of F hF) (isInducing_of F hF)
    dense := denseRange_of F hF }

/-- The source completion is canonically the coherent-residue inverse limit. -/
noncomputable def completionAddEquiv :
    letI : TopologicalSpace G := topologyOfAntitone F hF
    letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
    letI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
    UniformSpace.Completion G ≃ₜ+ Completion F hF := by
  let : TopologicalSpace G := topologyOfAntitone F hF
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  let : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  let e : UniformSpace.Completion G ≃ᵤ Completion F hF :=
    (UniformSpace.Completion.cPkg (α := G)).compareEquiv (abstractCompletion F hF)
  exact { e.toHomeomorph with
    map_add' := ((of F hF).extension (continuous_of F hF)).map_add }

/-- The completion comparison extends the original diagonal map. -/
theorem completionAddEquiv_coe (x : G) :
    letI : TopologicalSpace G := topologyOfAntitone F hF
    letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
    letI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
    completionAddEquiv F hF (x : UniformSpace.Completion G) = of F hF x := by
  let : TopologicalSpace G := topologyOfAntitone F hF
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  let : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  exact (UniformSpace.Completion.cPkg (α := G)).compare_coe (abstractCompletion F hF) x

end Completion


-- The source's p-adic prototype: the powers of `2` give a descending subgroup family.
example : Antitone (fun n : ℕ => AddSubgroup.zmultiples ((2 : ℤ) ^ n)) := by
  intro m n hmn
  rw [AddSubgroup.zmultiples_le, AddSubgroup.mem_zmultiples_iff]
  obtain ⟨c, hc⟩ := pow_dvd_pow (2 : ℤ) hmn
  refine ⟨c, ?_⟩
  simpa [zsmul_eq_mul, mul_comm] using hc.symm

-- Without separation, the diagonal map need not be injective: the constant top family
-- gives the indiscrete subgroup topology and collapses every residue quotient.
example : ¬ Function.Injective
    (Completion.of (fun _ : ℕ => (⊤ : AddSubgroup ℤ)) (fun _ _ _ => le_rfl)) := by
  intro h
  apply (show (0 : ℤ) ≠ 1 by norm_num)
  apply h
  apply Subtype.ext
  funext n
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  simp
end AddSubgroup
