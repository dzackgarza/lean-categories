/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

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

/-- Serre's unramified intermediate-field datum (FC10-C04-U012): the fixed
field of the inertia subgroup, viewed inside the full `K`-automorphism group
of `L`.

The assertion that this fixed field is the largest unramified subextension is
result content and is not bundled into the Sweep-III declaration. -/
noncomputable def serreUnramifiedFixedFieldData (A : ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField <|
    (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

/-- A chosen DVR element serving as Serre's uniformizer datum
(FC10-C04-U012).

Its irreducibility / maximal-ideal-generator property is supplied by the
existing DVR theory and remains outside this data declaration. -/
noncomputable def serreUniformizerData
    (A : ValuationSubring L) [IsDiscreteValuationRing A] : A :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible A)

end LeanCategories.Algebra
