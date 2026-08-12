/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IntegralAdeleRing
public import LeanCategories.ForMathlib.AdicCompletionLocallyCompact
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Integral general linear groups inside finite adelic groups

The integral subgroup is the image of general linear matrices over the finite integral adele
ring. Its elements are exactly the invertible adelic matrices whose matrix and inverse matrix
have integral entries.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace LeanCategories.Algebra

universe u v

variable (K : Type u) [Field K] [NumberField K]
variable (I : Type v) [Fintype I] [DecidableEq I]

abbrev FiniteIntegralCoefficientRing := FiniteIntegralAdeleRing (𝓞 K) K
abbrev FiniteAdeleCoefficientRing := FiniteAdeleRing (𝓞 K) K

/-- Scalar extension embeds integral invertible matrices into finite adelic invertible matrices. -/
def finiteIntegralGeneralLinearHom :
    Matrix.GeneralLinearGroup I (FiniteIntegralCoefficientRing K) →*
      Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K) :=
  Matrix.GeneralLinearGroup.map
    (FiniteIntegralAdeleRing.inclusion (𝓞 K) K).toRingHom

/-- The finite integral general linear subgroup inside the adelic general linear group. -/
abbrev FiniteIntegralGeneralLinearSubgroup :
    Subgroup (Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K)) :=
  (finiteIntegralGeneralLinearHom K I).range

theorem mem_finiteIntegralGeneralLinearSubgroup_iff
    (g : Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K)) :
    g ∈ FiniteIntegralGeneralLinearSubgroup K I ↔
      (g : Matrix I I (FiniteAdeleCoefficientRing K)) ∈
          (Set.range (FiniteIntegralAdeleRing.inclusion (𝓞 K) K)).matrix ∧
        ((g⁻¹ : Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K)) :
          Matrix I I (FiniteAdeleCoefficientRing K)) ∈
          (Set.range (FiniteIntegralAdeleRing.inclusion (𝓞 K) K)).matrix := by
  constructor
  · rintro ⟨h, rfl⟩
    constructor <;> intro i j
    · exact ⟨h i j, rfl⟩
    · exact ⟨(h⁻¹) i j, rfl⟩
  · rintro ⟨hg, hgInv⟩
    let A : Matrix I I (FiniteIntegralCoefficientRing K) :=
      fun i j => Classical.choose (hg i j)
    let B : Matrix I I (FiniteIntegralCoefficientRing K) :=
      fun i j => Classical.choose (hgInv i j)
    have hA (i j : I) :
        FiniteIntegralAdeleRing.inclusion (𝓞 K) K (A i j) = g i j :=
      Classical.choose_spec (hg i j)
    have hB (i j : I) :
        FiniteIntegralAdeleRing.inclusion (𝓞 K) K (B i j) = g⁻¹ i j :=
      Classical.choose_spec (hgInv i j)
    let f := (FiniteIntegralAdeleRing.inclusion (𝓞 K) K).toRingHom
    have hf : Function.Injective f :=
      FiniteIntegralAdeleRing.inclusion_injective (𝓞 K) K
    have hAf : Matrix.map A f = (g : Matrix I I (FiniteAdeleCoefficientRing K)) := by
      apply Matrix.ext
      intro i j
      change FiniteIntegralAdeleRing.inclusion (𝓞 K) K (A i j) = g i j
      exact hA i j
    have hBf : Matrix.map B f =
        ((g⁻¹ : Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K)) :
          Matrix I I (FiniteAdeleCoefficientRing K)) := by
      apply Matrix.ext
      intro i j
      change FiniteIntegralAdeleRing.inclusion (𝓞 K) K (B i j) = g⁻¹ i j
      exact hB i j
    have hAB : (A : Matrix I I (FiniteIntegralCoefficientRing K)) * B = 1 := by
      apply Matrix.map_injective hf
      change Matrix.map (A * B) f = Matrix.map 1 f
      simp only [Matrix.map_mul]
      rw [hAf, hBf]
      simp
    have hBA : (B : Matrix I I (FiniteIntegralCoefficientRing K)) * A = 1 := by
      apply Matrix.map_injective hf
      change Matrix.map (B * A) f = Matrix.map 1 f
      simp only [Matrix.map_mul]
      rw [hBf, hAf]
      simp
    let h : Matrix.GeneralLinearGroup I (FiniteIntegralCoefficientRing K) :=
      ⟨A, B, hAB, hBA⟩
    refine ⟨h, ?_⟩
    apply Units.val_injective
    exact Matrix.ext hA

/-- The finite integral general linear subgroup is open in the adelic general linear group. -/
theorem isOpen_finiteIntegralGeneralLinearSubgroup :
    IsOpen (FiniteIntegralGeneralLinearSubgroup K I :
      Set (Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K))) := by
  have hset :
      (FiniteIntegralGeneralLinearSubgroup K I :
          Set (Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K))) =
        {g : Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K) |
          (g : Matrix I I (FiniteAdeleCoefficientRing K)) ∈
              (Set.range (FiniteIntegralAdeleRing.inclusion (𝓞 K) K)).matrix ∧
            ((g⁻¹ : Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K)) :
              Matrix I I (FiniteAdeleCoefficientRing K)) ∈
              (Set.range (FiniteIntegralAdeleRing.inclusion (𝓞 K) K)).matrix} :=
    Set.ext fun g => mem_finiteIntegralGeneralLinearSubgroup_iff K I g
  rw [hset]
  exact ((FiniteIntegralAdeleRing.isOpen_range_inclusion (𝓞 K) K).matrix.preimage
      Units.continuous_val).inter
    ((FiniteIntegralAdeleRing.isOpen_range_inclusion (𝓞 K) K).matrix.preimage
      Units.continuous_coe_inv)

/-- The finite integral general linear subgroup is compact. -/
theorem isCompact_finiteIntegralGeneralLinearSubgroup :
    IsCompact (FiniteIntegralGeneralLinearSubgroup K I :
      Set (Matrix.GeneralLinearGroup I (FiniteAdeleCoefficientRing K))) := by
  letI (v : HeightOneSpectrum (𝓞 K)) :
      CompactSpace (v.adicCompletionIntegers K) :=
    HeightOneSpectrum.compactSpaceAdicCompletionIntegers K v
  letI : CompactSpace (FiniteIntegralCoefficientRing K) := Pi.compactSpace
  letI : CompactSpace (Matrix I I (FiniteIntegralCoefficientRing K)) := Pi.compactSpace
  change IsCompact (Set.range (finiteIntegralGeneralLinearHom K I))
  rw [← Set.image_univ]
  exact isCompact_univ.image <|
    (FiniteIntegralAdeleRing.inclusion (𝓞 K) K).cont.generalLinearGroup_map

end LeanCategories.Algebra
