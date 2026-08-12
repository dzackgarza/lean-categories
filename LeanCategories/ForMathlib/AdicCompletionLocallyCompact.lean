/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.DenseIntegralCompletion
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Local compactness of height-one completions of number fields

The residue field of a completed local integer ring equals the residue field of the original
height-one prime. The latter is finite for a number ring. Completeness and the discrete valuation
ring structure then imply compactness of the integer ring and local compactness of the field.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped NumberField
open scoped Valued

namespace IsDedekindDomain.HeightOneSpectrum

universe u

variable (K : Type u) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- The residue field of the completed local ring is the original prime quotient. -/
noncomputable def quotientEquivAdicCompletionResidueField :
    ((𝓞 K) ⧸ v.asIdeal) ≃+* (𝓀[v.adicCompletion K]) := by
  change ((𝓞 K) ⧸ v.asIdeal) ≃+*
    (v.adicCompletionIntegers K ⧸
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
  rw [← pow_one v.asIdeal,
    ← pow_one (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))]
  exact quotientPowEquivAdicCompletionIntegers K v 1

/-- The completed local residue field is finite. -/
instance finiteAdicCompletionResidueField : Finite (𝓀[v.adicCompletion K]) := by
  letI : Finite ((𝓞 K) ⧸ v.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  exact Finite.of_equiv ((𝓞 K) ⧸ v.asIdeal)
    (quotientEquivAdicCompletionResidueField K v).toEquiv

/-- The completed local integer ring is complete. -/
instance completeSpaceAdicCompletionIntegers :
    CompleteSpace (v.adicCompletionIntegers K) :=
  (Valued.isClosed_valuationSubring (v.adicCompletion K)).completeSpace_coe

/-- The completed local integer ring is compact. -/
instance compactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) := by
  change CompactSpace 𝒪[v.adicCompletion K]
  letI : IsDiscreteValuationRing 𝒪[v.adicCompletion K] := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  exact
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField).mpr
      ⟨completeSpaceAdicCompletionIntegers K v, inferInstance,
        finiteAdicCompletionResidueField K v⟩

/-- A height-one completion of a number field is a proper metric space. -/
instance properSpaceAdicCompletion : ProperSpace (v.adicCompletion K) :=
  Valued.integer.properSpace_iff_compactSpace_integer.mpr
    (compactSpaceAdicCompletionIntegers K v)

/-- A height-one completion of a number field is locally compact. -/
instance locallyCompactSpaceAdicCompletion :
    LocallyCompactSpace (v.adicCompletion K) :=
  inferInstance

end IsDedekindDomain.HeightOneSpectrum
