/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Adic completeness of local integer rings

This proof follows `AdicCompletionIsAdic.lean` from `DE0CH/flt-lean`, revision
`e9d6cf12041110ab8c235849577eebb6aba2ea14`.
-/

@[expose] public section

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

instance instIsUniformAddGroupAdicCompletionIntegers :
    IsUniformAddGroup (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsUniformAddGroup (v.adicCompletionIntegers K).toSubring.toAddSubgroup)

instance instIsTopologicalRingAdicCompletionIntegers :
    IsTopologicalRing (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsTopologicalRing (v.adicCompletionIntegers K).toSubring)

/-- The subspace topology on the local integers is its maximal-ideal-adic topology. -/
theorem isAdic_maximalIdeal_adicCompletionIntegers :
    IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hint := HeightOneSpectrum.adicCompletionIntegers.integers K v
  have hpow : ∀ n : ℕ,
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
          Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) =
        {y : v.adicCompletionIntegers K |
          Valued.v (y : v.adicCompletion K) ≤
            Valued.v ((ϖ ^ n : _) : v.adicCompletion K)} := by
    intro n
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.span_singleton_pow,
      Valuation.Integers.coe_span_singleton_eq_setOf_le_v_algebraMap hint]
    rfl
  have hϖ0 : ∀ n : ℕ, Valued.v ((ϖ ^ n : _) : v.adicCompletion K) ≠ 0 := by
    intro n
    simpa using
      (hint.valuation_pos_iff_ne_zero (x := ϖ ^ n)).mpr
        (pow_ne_zero n hϖ.ne_zero) |>.ne'
  rw [isAdic_iff]
  refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hpow n]
    have hset : {y : v.adicCompletionIntegers K |
        Valued.v (y : v.adicCompletion K) ≤
          Valued.v ((ϖ ^ n : _) : v.adicCompletion K)} =
      Subtype.val ⁻¹' {x : v.adicCompletion K |
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict x ≤
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
            ((ϖ ^ n : _) : v.adicCompletion K)} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_preimage,
          Valuation.restrict_le_iff]
    rw [hset]
    exact (Valued.isOpen_closedBall _ (by simpa using hϖ0 n)).preimage
      continuous_subtype_val
  · rw [mem_nhds_subtype] at hs
    obtain ⟨t, ht, hts⟩ := hs
    rw [ZeroMemClass.coe_zero] at ht
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp ht
    obtain ⟨n, hn⟩ := exists_pow_lt₀
      (hint.valuation_irreducible_lt_one hϖ)
      (Units.mk0 (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
        (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ))
    refine ⟨n, fun y hy ↦ ?_⟩
    refine hts (hγ ?_)
    show (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
      (y : v.adicCompletion K) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    calc
      Valued.v (y : v.adicCompletion K)
          ≤ Valued.v ((ϖ ^ n : _) : v.adicCompletion K) := by
            rw [hpow n] at hy
            exact hy
      _ = Valued.v ((ϖ : _) : v.adicCompletion K) ^ n := by
            push_cast
            simp
      _ < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := hn

/-- The local integer ring is complete for its maximal-ideal-adic topology. -/
theorem isAdicComplete_maximalIdeal_adicCompletionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  (IsAdic.isAdicComplete_iff
    (isAdic_maximalIdeal_adicCompletionIntegers K v)).mpr
      ⟨(Valued.isClosed_valuationSubring
        (v.adicCompletion K)).completeSpace_coe, inferInstance⟩

end IsDedekindDomain.HeightOneSpectrum
