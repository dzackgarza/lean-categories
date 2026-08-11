/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.AdicCompletionIntegers

/-!
# Density of global integers in a local completion
-/

@[expose] public section

open scoped WithZero
open WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- The global integers are dense in the integer ring of each finite completion. -/
theorem denseRange_algebraMap_adicCompletionIntegers :
    DenseRange (algebraMap R (v.adicCompletionIntegers K)) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro y
  rw [mem_closure_iff_nhds']
  intro s hs
  rw [mem_nhds_subtype] at hs
  obtain ⟨t, ht, hts⟩ := hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  let δ := min γ 1
  have hδ : {z : v.adicCompletion K |
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
        (z - (y : v.adicCompletion K)) < δ.1} ∈ nhds (y : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    exact ⟨δ, Set.Subset.rfl⟩
  obtain ⟨x, hx⟩ := (denseRange_algebraMap (R := R) K v).mem_nhds hδ
  have hx' : Valued.v ((algebraMap K (v.adicCompletion K)) x -
      (y : v.adicCompletion K)) <
      MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := by
    simpa only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] using hx
  have hδ_one : MonoidWithZeroHom.ValueGroup₀.embedding δ.1 ≤ (1 : ℤᵐ⁰) := by
    have h := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.monotone
      (show δ.1 ≤ (1 : MonoidWithZeroHom.ValueGroup₀
        (MonoidWithZeroHom.ofClass
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))) by simp [δ, Units.min_val])
    simpa using h
  have hx_integer : v.valuation K x ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation' (v := v)]
    calc
      Valued.v (x : v.adicCompletion K) ≤
          max (Valued.v ((x : v.adicCompletion K) - (y : v.adicCompletion K)))
            (Valued.v (y : v.adicCompletion K)) := by
            conv_lhs => rw [← sub_add_cancel (x : v.adicCompletion K) y]
            exact Valuation.map_add _ _ _
      _ ≤ 1 := max_le (hx'.le.trans hδ_one) y.2
  let ε : (ℤᵐ⁰)ˣ := Units.mk0
    (MonoidWithZeroHom.ValueGroup₀.embedding δ.1)
    (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero δ)
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hx_integer ε
  have ha' : Valued.v ((algebraMap R (v.adicCompletion K)) a -
      (algebraMap K (v.adicCompletion K)) x) <
      MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := by
    calc
      Valued.v ((algebraMap R (v.adicCompletion K)) a -
          (algebraMap K (v.adicCompletion K)) x) =
          v.valuation K (algebraMap R K a - x) := by
            rw [← valuedAdicCompletion_eq_valuation' (v := v)]
            congr 1
            simpa [algebraMap_adicCompletion] using
              (map_sub (algebraMap K (v.adicCompletion K))
                (algebraMap R K a) x).symm
      _ < MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := by
        simpa [ε] using ha
  let z : Set.range (algebraMap R (v.adicCompletionIntegers K)) :=
    ⟨algebraMap R (v.adicCompletionIntegers K) a, Set.mem_range_self a⟩
  refine ⟨z, hts (hγ ?_)⟩
  change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
    ((algebraMap R (v.adicCompletion K)) a - y) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  calc
    Valued.v ((algebraMap R (v.adicCompletion K)) a - y) ≤
        max (Valued.v ((algebraMap R (v.adicCompletion K)) a -
          (algebraMap K (v.adicCompletion K)) x))
          (Valued.v ((algebraMap K (v.adicCompletion K)) x - y)) := by
            rw [← sub_add_sub_cancel]
            exact Valuation.map_add _ _ _
    _ < MonoidWithZeroHom.ValueGroup₀.embedding δ.1 := max_lt ha' hx'
    _ ≤ MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
      exact MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.monotone
        (by simp [δ, Units.min_val])

/-- Pulling a power of the local maximal ideal back to `R` gives the matching prime power. -/
theorem comap_pow_maximalIdeal_adicCompletionIntegers (n : ℕ) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n).comap
      (algebraMap R (v.adicCompletionIntegers K)) = v.asIdeal ^ n := by
  let f : R →+*
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring :=
    algebraMap R (v.adicCompletionIntegers K)
  obtain ⟨r, hr, hr₂⟩ := Ideal.exists_mem_pow_notMem_pow_succ
    v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have hr' : r ∈ v.asIdeal := by simpa using hr
  have hr₂' : r ∉ v.asIdeal ^ 2 := by simpa using hr₂
  have hr₀ : r ≠ 0 := by
    intro h
    exact hr₂' (h ▸ (v.asIdeal ^ 2).zero_mem)
  have hval_le : v.intValuation r ≤ exp (-1 : ℤ) :=
    (v.intValuation_le_pow_iff_mem r 1).2 (by simpa using hr')
  have hemult_le : emultiplicity v.asIdeal (Ideal.span {r}) ≤ 1 := by
    apply (ENat.lt_coe_add_one_iff (n := 1)).mp
    apply lt_of_not_ge
    intro h
    exact hr₂' ((v.intValuation_le_pow_iff_mem r 2).1
      ((v.intValuation_le_exp_iff_le_emultiplicity (r := r) (n := 2)).2 h))
  have hval_ge : exp (-1 : ℤ) ≤ v.intValuation r :=
    (v.exp_le_intValuation_iff_emultiplicity_le (r := r) (n := 1)).2 hemult_le
  have hval : v.intValuation r = exp (-1 : ℤ) := le_antisymm hval_le hval_ge
  let ϖ : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring :=
    f r
  have hϖval : Valued.v (ϖ : v.adicCompletion K) = exp (-1 : ℤ) := by
    calc
      Valued.v (ϖ : v.adicCompletion K) = v.valuation K (algebraMap R K r) := by
        exact valuedAdicCompletion_eq_valuation' (v := v) (k := algebraMap R K r)
      _ = v.intValuation r := v.valuation_of_algebraMap r
      _ = exp (-1 : ℤ) := hval
  have hgen :
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) =
          Units.mk0 (exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      ⟨(ϖ : v.adicCompletion K), hϖval⟩
  have hϖ : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer ϖ := by
    rw [Valuation.IsUniformizer.iff, hgen]
    simpa only [Units.val_mk0] using hϖval
  change ((IsLocalRing.maximalIdeal
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring ^ n).comap
      f) = v.asIdeal ^ n
  rw [Valuation.IsUniformizer.is_generator hϖ, Ideal.span_singleton_pow]
  ext x
  rw [Ideal.mem_comap]
  have hspan : f x ∈ Ideal.span {ϖ ^ n} ↔
      Valued.v (f x : v.adicCompletion K) ≤
        Valued.v ((ϖ ^ n :
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring) :
            v.adicCompletion K) := by
    change f x ∈ (Ideal.span {ϖ ^ n} : Set _) ↔ _
    exact Set.ext_iff.mp (Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe
      (ϖ ^ n)) (f x)
  rw [hspan]
  rw [show Valued.v (f x : v.adicCompletion K) = v.intValuation x by
        exact (valuedAdicCompletion_eq_valuation' (v := v)
          (k := algebraMap R K x)).trans (v.valuation_of_algebraMap x),
    show Valued.v ((ϖ ^ n :
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring) :
        v.adicCompletion K) = Valued.v (ϖ : v.adicCompletion K) ^ n by
      rw [show ((ϖ ^ n :
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring) :
          v.adicCompletion K) = (ϖ : v.adicCompletion K) ^ n by norm_cast,
        map_pow],
    hϖval]
  simpa using v.intValuation_le_pow_iff_mem x n

/-- The quotient of `R` by `v ^ n` is the matching quotient of the local integer ring. -/
noncomputable def quotientPowEquivAdicCompletionIntegers (n : ℕ) :
    (R ⧸ (v.asIdeal ^ n)) ≃+*
      (v.adicCompletionIntegers K ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)) := by
  let I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n
  let f := algebraMap R (v.adicCompletionIntegers K)
  have hcomap : I.comap f = v.asIdeal ^ n := by
    exact comap_pow_maximalIdeal_adicCompletionIntegers K v n
  let q : (R ⧸ (v.asIdeal ^ n)) →+* (v.adicCompletionIntegers K ⧸ I) :=
    Ideal.quotientMap I f hcomap.symm.le
  have hinj : Function.Injective q :=
    Ideal.quotientMap_injective' hcomap.le
  have hopen : IsOpen (I : Set (v.adicCompletionIntegers K)) := by
    exact (isAdic_iff.mp (isAdic_maximalIdeal_adicCompletionIntegers K v)).1 n
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    let U : Set (v.adicCompletionIntegers K) := {x | x - y ∈ I}
    have hUopen : IsOpen U := hopen.preimage (continuous_id.sub continuous_const)
    have hy : y ∈ U := by simp [U]
    obtain ⟨r, hr⟩ := (denseRange_algebraMap_adicCompletionIntegers K v).mem_nhds
      (hUopen.mem_nhds hy)
    refine ⟨Ideal.Quotient.mk (v.asIdeal ^ n) r, ?_⟩
    change Ideal.Quotient.mk I (f r) = Ideal.Quotient.mk I y
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hr
  exact RingEquiv.ofBijective q ⟨hinj, hsurj⟩

end IsDedekindDomain.HeightOneSpectrum
