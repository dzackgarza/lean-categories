/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.RadicalData
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Iterated unipotent-normalizer data

Definition-level realization of the construction clause in Humphreys
FC16-C10-U044.

Starting with a closed unipotent subgroup `U`, the source repeatedly replaces
the current subgroup by the unipotent radical of its normalizer. Once this
sequence stabilizes, the normalizer at that stage is denoted `P(U)`. Sweep
III records the sequence by its exact successor graph using certified radical
data; no recursive arbitrary radical choice is made. Finite stabilization is
a result-layer theorem.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Source-faithful data for the recursive sequence
`U_0=U`, `U_(n+1)=R_u(N_G(U_n))`. -/
structure UnipotentNormalizerSequenceData
    (isUnipotentElement : G → Prop) (U : Subgroup G) where
  term : ℕ → Subgroup G
  zero : term 0 = U
  successor : ∀ n : ℕ,
    let N := Subgroup.normalizer (term n : Set G)
    ∃ R : UnipotentRadicalData (G := N) (fun x : N => isUnipotentElement x.1),
      term (n + 1) = R.1.map N.subtype

/-- The normalizer attached to the `n`-th unipotent term. -/
noncomputable def unipotentNormalizerAt
    (isUnipotentElement : G → Prop) (U : Subgroup G)
    (D : UnipotentNormalizerSequenceData isUnipotentElement U)
    (n : ℕ) : Subgroup G :=
  Subgroup.normalizer
    (D.term n : Set G)

/-- Stage `n` is a stabilization stage when the next unipotent term is the
same subgroup. -/
def IsUnipotentNormalizerStabilizationStage
    (isUnipotentElement : G → Prop) (U : Subgroup G)
    (D : UnipotentNormalizerSequenceData isUnipotentElement U)
    (n : ℕ) : Prop :=
  D.term (n + 1) = D.term n

/-- A supplied subgroup `P` is a terminal normalizer for the construction
when it is the normalizer at some stabilization stage.

This relation does not assert that such a finite stage exists. -/
def IsTerminalUnipotentNormalizer
    (isUnipotentElement : G → Prop) (U P : Subgroup G)
    (D : UnipotentNormalizerSequenceData isUnipotentElement U) : Prop :=
  ∃ n : ℕ,
    IsUnipotentNormalizerStabilizationStage isUnipotentElement U D n ∧
      P = unipotentNormalizerAt isUnipotentElement U D n

end LeanCategories.AlgebraicGeometry
