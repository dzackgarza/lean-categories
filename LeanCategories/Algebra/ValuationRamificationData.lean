/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Valuation ramification congruence data

Definition-level realization of the non-native clause in Neukirch
FC09-C02-U106.

Mathlib already owns the decomposition and inertia subgroups of a valuation
subring.  Neukirch's additional ramification group is cut out inside the
decomposition group by the congruences `σ x / x ≡ 1` modulo the maximal ideal.

Sweep III records that congruence locus as a set.  Showing that it is a
subgroup, identifying it with a lower ramification group `G₁`, and proving its
functorial properties are result content.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Algebra

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The maximal ideal of a valuation subring, viewed as a literal subset of the
ambient field rather than as its ideal-theoretic extension to that field. -/
def valuationMaximalIdealImage (A : ValuationSubring L) : Set L :=
  (fun a : A => (a : L)) '' (IsLocalRing.maximalIdeal A : Set A)

/-- Raw Neukirch ramification congruence locus inside the decomposition group.

An automorphism belongs when `σ x / x - 1` is represented by an element of the
maximal ideal of the valuation ring for every nonzero `x`. -/
def valuationRamificationSet (A : ValuationSubring L) :
    Set (A.decompositionSubgroup K) :=
  {σ | ∀ x : Lˣ,
    σ.1 (x : L) / (x : L) - 1 ∈ valuationMaximalIdealImage A}

end LeanCategories.Algebra
