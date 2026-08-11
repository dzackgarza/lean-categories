/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.AdicCompletionIntegers
public import Mathlib.RingTheory.AdicCompletion.RingHom

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

theorem quotientPowEquivAdicCompletionIntegers_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) hmn).comp
        (quotientPowEquivAdicCompletionIntegers K v n).toRingHom =
      (quotientPowEquivAdicCompletionIntegers K v m).toRingHom.comp
        (Ideal.Quotient.factorPow v.asIdeal hmn) := by
  apply DFunLike.ext _ _
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem quotientPowEquivAdicCompletionIntegers_symm_compatible {m n : ℕ}
    (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow v.asIdeal hmn).comp
        (quotientPowEquivAdicCompletionIntegers K v n).symm.toRingHom =
      (quotientPowEquivAdicCompletionIntegers K v m).symm.toRingHom.comp
        (Ideal.Quotient.factorPow
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) hmn) := by
  ext z
  apply (quotientPowEquivAdicCompletionIntegers K v m).injective
  change (quotientPowEquivAdicCompletionIntegers K v m)
      (Ideal.Quotient.factorPow v.asIdeal hmn
        ((quotientPowEquivAdicCompletionIntegers K v n).symm
          (Ideal.Quotient.mk _ z))) =
    (quotientPowEquivAdicCompletionIntegers K v m)
      ((quotientPowEquivAdicCompletionIntegers K v m).symm
        (Ideal.Quotient.factorPow
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) hmn
            (Ideal.Quotient.mk _ z)))
  rw [RingEquiv.apply_symm_apply]
  have h := RingHom.congr_fun
      (quotientPowEquivAdicCompletionIntegers_compatible K v hmn)
        ((quotientPowEquivAdicCompletionIntegers K v n).symm
          (Ideal.Quotient.mk _ z))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe] at h
  change Ideal.Quotient.factorPow
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) hmn
        ((quotientPowEquivAdicCompletionIntegers K v n)
          ((quotientPowEquivAdicCompletionIntegers K v n).symm
            (Ideal.Quotient.mk _ z))) = _ at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

omit [IsDedekindDomain R] in
theorem factorPow_eval_adicCompletion {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion v.asIdeal R) :
    Ideal.Quotient.factorPow v.asIdeal hmn
      (AdicCompletion.evalₐ v.asIdeal n x) =
        AdicCompletion.evalₐ v.asIdeal m x := by
  let hm : (v.asIdeal ^ m • ⊤ : Ideal R) = v.asIdeal ^ m := Ideal.mul_top _
  apply (Ideal.quotientEquivAlgOfEq R hm).symm.injective
  simp only [Ideal.quotientEquivAlgOfEq_symm]
  change Ideal.Quotient.factor (le_of_eq hm.symm)
      (Ideal.Quotient.factorPow v.asIdeal hmn
        (AdicCompletion.evalₐ v.asIdeal n x)) =
    Ideal.Quotient.factor (le_of_eq hm.symm)
      (AdicCompletion.evalₐ v.asIdeal m x)
  rw [AdicCompletion.factor_evalₐ_eq_eval (I := v.asIdeal) (R := R) x
    (le_of_eq hm.symm)]
  change Ideal.Quotient.factor (le_of_eq hm.symm)
      (Ideal.Quotient.factorPow v.asIdeal hmn
        (AdicCompletion.evalₐ v.asIdeal n x)) = x.1 m
  rw [← x.2 hmn]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ v.asIdeal n x)
  have hraw := AdicCompletion.factor_evalₐ_eq_eval
    (I := v.asIdeal) (R := R) x
      (show v.asIdeal ^ n ≤ v.asIdeal ^ n • ⊤ by simp)
  rw [← hr] at hraw ⊢
  change Ideal.Quotient.factor _ (Ideal.Quotient.mk _ r) = x.1 n at hraw
  rw [← hraw]
  simp [AdicCompletion.transitionMap, Ideal.Quotient.factorPow]

/-- The completion of `R` at `v` maps to the complete local integer ring through its
compatible residue quotients. -/
noncomputable def adicCompletionToIntegers :
    AdicCompletion v.asIdeal R →+* v.adicCompletionIntegers K := by
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
    isAdicComplete_maximalIdeal_adicCompletionIntegers K v
  exact IsAdicComplete.liftRingHom
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
    (fun n ↦ (quotientPowEquivAdicCompletionIntegers K v n).toRingHom.comp
      (AdicCompletion.evalₐ v.asIdeal n).toRingHom)
    (fun {m n} hmn ↦ by
      ext x
      simp only [RingHom.comp_apply]
      calc
        _ = quotientPowEquivAdicCompletionIntegers K v m
            (Ideal.Quotient.factorPow v.asIdeal hmn
              (AdicCompletion.evalₐ v.asIdeal n x)) :=
          RingHom.congr_fun
            (quotientPowEquivAdicCompletionIntegers_compatible K v hmn)
              (AdicCompletion.evalₐ v.asIdeal n x)
        _ = _ := congrArg (quotientPowEquivAdicCompletionIntegers K v m)
          (factorPow_eval_adicCompletion v hmn x))

/-- The complete local integer ring maps back to the prime-adic completion through the
inverse residue quotient equivalences. -/
noncomputable def integersToAdicCompletion :
    v.adicCompletionIntegers K →+* AdicCompletion v.asIdeal R :=
  AdicCompletion.liftRingHom v.asIdeal
    (fun n ↦ (quotientPowEquivAdicCompletionIntegers K v n).symm.toRingHom.comp
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers K) ^ n)))
    (fun {m n} hmn ↦ by
      ext x
      simpa only [RingHom.comp_apply, Ideal.Quotient.factor_mk] using
        RingHom.congr_fun
          (quotientPowEquivAdicCompletionIntegers_symm_compatible K v hmn)
            (Ideal.Quotient.mk _ x))

@[simp]
theorem mk_adicCompletionToIntegers (n : ℕ) (x : AdicCompletion v.asIdeal R) :
    Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
        (adicCompletionToIntegers K v x) =
      quotientPowEquivAdicCompletionIntegers K v n
        (AdicCompletion.evalₐ v.asIdeal n x) := by
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
    isAdicComplete_maximalIdeal_adicCompletionIntegers K v
  exact IsAdicComplete.mk_liftRingHom _ _ _ n x

@[simp]
theorem eval_integersToAdicCompletion (n : ℕ) (x : v.adicCompletionIntegers K) :
    AdicCompletion.evalₐ v.asIdeal n (integersToAdicCompletion K v x) =
      (quotientPowEquivAdicCompletionIntegers K v n).symm
        (Ideal.Quotient.mk _ x) := by
  exact AdicCompletion.evalₐ_liftRingHom _ _ _ n x

/-- The prime-adic completion of `R` is its valuation ring inside the completed fraction field. -/
noncomputable def adicCompletionEquivAdicCompletionIntegers :
    AdicCompletion v.asIdeal R ≃+* v.adicCompletionIntegers K := by
  letI : IsAdicComplete
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
    isAdicComplete_maximalIdeal_adicCompletionIntegers K v
  exact {
  toFun := adicCompletionToIntegers K v
  invFun := integersToAdicCompletion K v
  left_inv x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [eval_integersToAdicCompletion, mk_adicCompletionToIntegers,
      RingEquiv.symm_apply_apply]
  right_inv x := by
    have h : (adicCompletionToIntegers K v).comp
        (integersToAdicCompletion K v) = RingHom.id _ := by
      apply DFunLike.ext _ _
      intro y
      apply congrFun (IsHausdorff.funext'
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
          (fun n z ↦ by
            simp [mk_adicCompletionToIntegers, eval_integersToAdicCompletion])) y
    exact RingHom.congr_fun h x
  map_add' := map_add (adicCompletionToIntegers K v)
  map_mul' := map_mul (adicCompletionToIntegers K v)
  }

end IsDedekindDomain.HeightOneSpectrum
