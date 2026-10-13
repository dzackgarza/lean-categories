/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Complex
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Archimedean local reciprocity data

Definition-level realization of Serre FC10-C14-U046.

For the real place, Serre writes the local reciprocity isomorphism

  `ℝˣ / N(ℂˣ) → Gal(ℂ/ℝ)`.

Sweep III records the literal norm quotient and the underlying reciprocity
function by its source graph: a positive real unit maps to the identity and a
negative real unit maps to complex conjugation. The facts that the norm image
is exactly the positive real units, that this graph descends uniquely, and
that the selected function is a group isomorphism are result-layer
statements and are not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- The complex norm on units, used in Serre's archimedean norm quotient. -/
def realComplexNormUnitsData : ℂˣ →* ℝˣ :=
  Units.map (Algebra.norm ℝ : ℂ →* ℝ)

/-- Serre's norm quotient `ℝˣ / N(ℂˣ)`. -/
abbrev realComplexNormQuotientData : Type :=
  ℝˣ ⧸ realComplexNormUnitsData.range

/-- The real absolute Galois group appearing in the archimedean local
reciprocity map. -/
abbrev realComplexGaloisGroupData : Type :=
  ℂ ≃ₐ[ℝ] ℂ

/-- Exact sign/conjugation graph characterizing Serre's real reciprocity
function on representatives. -/
def IsRealComplexReciprocityData
    (f : realComplexNormQuotientData → realComplexGaloisGroupData) : Prop :=
  ∀ x : ℝˣ,
    f (QuotientGroup.mk x) =
      if 0 < (x : ℝ) then AlgEquiv.refl else Complex.conjAe

/-- The underlying function of Serre's real/complex local reciprocity
isomorphism, selected by its sign/conjugation graph.

The theorem layer proves that the selected function satisfies this graph and
upgrades it to the stated group isomorphism. -/
def realComplexReciprocityData :
    realComplexNormQuotientData → realComplexGaloisGroupData := by
  letI : Nonempty
      (realComplexNormQuotientData → realComplexGaloisGroupData) :=
    ⟨fun _ => AlgEquiv.refl⟩
  exact Classical.epsilon IsRealComplexReciprocityData

end LeanCategories.Algebra
