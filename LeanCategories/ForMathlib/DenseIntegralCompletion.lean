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

end IsDedekindDomain.HeightOneSpectrum
