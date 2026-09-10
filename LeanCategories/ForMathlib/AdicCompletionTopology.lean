/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import LeanCategories.ForMathlib.AdicModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# The inverse-limit topology on adic completions of rings and modules

Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), printed p. 105,
FC04-C10-U018–U019. The discrete quotients `M / IⁿM` give the completion its
inverse-limit topology. Addition and the action of the completed ring are continuous.
Linear maps are continuous for the adic topologies and induce continuous completed maps.

The completion, quotient maps, and completed scalar action are Mathlib's. The ring
case uses this same topology, with its normalized projections to `R / Iⁿ` compared
explicitly to the module projections. This is the inverse-limit topology, not an
assertion that powers of the extended ideal define it without further hypotheses.
-/

@[expose] public section

noncomputable section

open Topology

namespace AdicCompletion

variable (R : Type*) [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The subspace topology on compatible families of discrete module residues. -/
instance adicCompletionTopologicalSpace : TopologicalSpace (AdicCompletion I M) := by
  let (n : ℕ) : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  exact TopologicalSpace.induced Subtype.val inferInstance

/-- Continuity into a completion is equivalent to continuity of every residue coordinate. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → AdicCompletion I M) :
    Continuous f ↔ ∀ n : ℕ, @Continuous X (M ⧸ (I ^ n • ⊤ : Submodule R M))
      inferInstance ⊥ (fun x => (f x).val n) := by
  let (n : ℕ) : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  constructor
  · intro h n
    exact (continuous_apply n).comp (continuous_induced_rng.mp h)
  · intro h
    exact continuous_induced_rng.mpr (continuous_pi h)

/-- The projections to discrete module quotients are continuous. -/
theorem continuous_eval_module (n : ℕ) :
    @Continuous (AdicCompletion I M) (M ⧸ (I ^ n • ⊤ : Submodule R M))
      inferInstance ⊥ (eval I M n) :=
  (continuous_iff R I M id).mp continuous_id n

/-- Distinct compatible residue families are separated by a discrete coordinate. -/
instance : T2Space (AdicCompletion I M) := by
  let (n : ℕ) : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  let (n : ℕ) : DiscreteTopology (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⟨rfl⟩
  apply Topology.IsEmbedding.t2Space (f := (submodule I M).subtype)
  exact ⟨⟨rfl⟩, Subtype.val_injective⟩

/-- Addition and negation are continuous coordinatewise. -/
instance : IsTopologicalAddGroup (AdicCompletion I M) := by
  let (n : ℕ) : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  let (n : ℕ) : DiscreteTopology (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⟨rfl⟩
  exact { ContinuousAdd.induced (submodule I M).subtype,
    ContinuousNeg.induced (submodule I M).subtype with }

/-- The completed ring acts jointly continuously on the completed module. -/
instance : ContinuousSMul (AdicCompletion I R) (AdicCompletion I M) := by
  refine ⟨(continuous_iff R I M _).mpr fun n => ?_⟩
  let : TopologicalSpace (R ⧸ (I ^ n • ⊤ : Ideal R)) := ⊥
  let : DiscreteTopology (R ⧸ (I ^ n • ⊤ : Ideal R)) := ⟨rfl⟩
  let : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  let : DiscreteTopology (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⟨rfl⟩
  exact (continuous_of_discreteTopology (f := fun p :
    (R ⧸ (I ^ n • ⊤ : Ideal R)) × (M ⧸ (I ^ n • ⊤ : Submodule R M)) =>
      p.1 • p.2)).comp
    (((continuous_eval_module R I R n).comp continuous_fst).prodMk
      ((continuous_eval_module R I M n).comp continuous_snd))

variable {M} {N : Type*} [AddCommGroup N] [Module R N]

/-- A linear map induces a continuous map of adic completions. -/
theorem continuous_map (f : M →ₗ[R] N) : Continuous (map I f) := by
  apply (continuous_iff R I N _).mpr
  intro n
  let : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  let : DiscreteTopology (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⟨rfl⟩
  let : TopologicalSpace (N ⧸ (I ^ n • ⊤ : Submodule R N)) := ⊥
  exact (continuous_of_discreteTopology (f := f.reduceModIdeal (I ^ n))).comp
    (continuous_eval_module R I M n)

/-- Ring operations are continuous for the same module inverse-limit topology. -/
instance : IsTopologicalRing (AdicCompletion I R) := by
  let (n : ℕ) : TopologicalSpace (R ⧸ (I ^ n • ⊤ : Ideal R)) := ⊥
  let (n : ℕ) : DiscreteTopology (R ⧸ (I ^ n • ⊤ : Ideal R)) := ⟨rfl⟩
  exact { ContinuousAdd.induced (subring I).subtype,
    ContinuousMul.induced (subring I).subtype,
    ContinuousNeg.induced (subring I).subtype with }

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

/-- The normalized projections to discrete ring quotients are continuous. -/
theorem continuous_eval (n : ℕ) :
    @Continuous (AdicCompletion I R) (R ⧸ I ^ n) inferInstance ⊥ (evalₐ I n) := by
  let : TopologicalSpace (R ⧸ (I ^ n • ⊤ : Ideal R)) := ⊥
  let : DiscreteTopology (R ⧸ (I ^ n • ⊤ : Ideal R)) := ⟨rfl⟩
  let : TopologicalSpace (R ⧸ I ^ n) := ⊥
  have h : I ^ n • ⊤ ≤ I ^ n := by simp
  have he : (fun x : AdicCompletion I R =>
    Submodule.factor h (eval I R n x)) = evalₐ I n := by
    funext x
    exact factor_eval_eq_evalₐ I x h
  rw [← he]
  exact continuous_of_discreteTopology.comp (continuous_eval_module R I R n)

/-- The ring topology is equally characterized by the normalized ring residues. -/
theorem continuous_iff_evalₐ {X : Type*} [TopologicalSpace X]
    (f : X → AdicCompletion I R) : Continuous f ↔
    ∀ n : ℕ, @Continuous X (R ⧸ I ^ n) inferInstance ⊥ (fun x => evalₐ I n (f x)) := by
  constructor
  · intro h n
    let : TopologicalSpace (R ⧸ I ^ n) := ⊥
    exact (continuous_eval R I n).comp h
  · intro h
    apply (continuous_iff R I R f).mpr
    intro n
    let : TopologicalSpace (R ⧸ I ^ n) := ⊥
    let : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩
    let : TopologicalSpace (R ⧸ (I ^ n • ⊤ : Ideal R)) := ⊥
    have hn : I ^ n ≤ I ^ n • ⊤ := by simp
    have he : (fun x => Ideal.Quotient.factor hn (evalₐ I n (f x))) =
        (fun x => (f x).val n) := by
      funext x
      exact factor_evalₐ_eq_eval I (f x) hn
    rw [← he]
    exact continuous_of_discreteTopology.comp (h n)

end AdicCompletion

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The canonical map from a module to its adic completion is continuous. -/
theorem continuous_of :
    @Continuous M (AdicCompletion I M) (I.adicModuleTopology M) inferInstance
      (of I M) := by
  let : TopologicalSpace M := I.adicModuleTopology M
  exact (continuous_iff R I M _).mpr fun n => I.continuous_quotient_mk_adicModule M n

/-- An adic Cauchy sequence converges to its class in the inverse-limit topology. -/
theorem tendsto_of_adicCauchySequence (a : AdicCauchySequence I M) :
    Filter.Tendsto (fun n => of I M (a n)) Filter.atTop (nhds (mk I M a)) := by
  let (n : ℕ) : TopologicalSpace (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⊥
  let (n : ℕ) : DiscreteTopology (M ⧸ (I ^ n • ⊤ : Submodule R M)) := ⟨rfl⟩
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro k
  rw [nhds_discrete, Filter.tendsto_pure]
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  exact AdicCauchySequence.mk_eq_mk hn a

/-- The original module is dense in its completion, without any injectivity assumption. -/
theorem denseRange_of : DenseRange (of I M) := by
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective I M x
  exact mem_closure_of_tendsto (tendsto_of_adicCauchySequence I M a)
    (Filter.Eventually.of_forall fun n => Set.mem_range_self (a n))

-- The same topology applies to actual module maps, not only to ring endomorphisms.
example (f : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ)) :
    Continuous (map (Ideal.span ({2} : Set ℤ)) f) :=
  continuous_map ℤ _ f

-- Density does not assert injectivity when the original adic topology is not separated.
example : ¬ Function.Injective (of (⊤ : Ideal ℤ) ℤ) := by
  intro h
  have he : of (⊤ : Ideal ℤ) ℤ 0 = of (⊤ : Ideal ℤ) ℤ 1 := by
    apply Subtype.ext
    funext n
    exact (Submodule.Quotient.eq _).mpr (by simp [Ideal.top_pow])
  exact zero_ne_one (h he)

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
