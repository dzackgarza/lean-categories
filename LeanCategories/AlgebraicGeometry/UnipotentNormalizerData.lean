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
the current subgroup by the unipotent radical of its normalizer.  Once this
sequence stabilizes, the normalizer at that stage is denoted `P(U)`.  Sweep
III records the recursive sequence and the terminal-stage relation.  Finite
stabilization, and hence existence of the source-named terminal normalizer,
is a result-layer theorem.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The recursive sequence `U_0 = U`,
`U_(n+1) = R_u(N_G(U_n))`, viewed as subgroups of the ambient group. -/
noncomputable def unipotentNormalizerSequence
    (isUnipotentElement : G → Prop) (U : Subgroup G) : ℕ → Subgroup G
  | 0 => U
  | n + 1 =>
      let N := Subgroup.normalizer
        (unipotentNormalizerSequence isUnipotentElement U n : Set G)
      (unipotentRadical (G := N) (fun x : N => isUnipotentElement x.1)).map N.subtype

/-- The normalizer attached to the `n`-th unipotent term. -/
noncomputable def unipotentNormalizerAt
    (isUnipotentElement : G → Prop) (U : Subgroup G) (n : ℕ) : Subgroup G :=
  Subgroup.normalizer
    (unipotentNormalizerSequence isUnipotentElement U n : Set G)

/-- Stage `n` is a stabilization stage when the next unipotent term is the
same subgroup. -/
def IsUnipotentNormalizerStabilizationStage
    (isUnipotentElement : G → Prop) (U : Subgroup G) (n : ℕ) : Prop :=
  unipotentNormalizerSequence isUnipotentElement U (n + 1) =
    unipotentNormalizerSequence isUnipotentElement U n

/-- A supplied subgroup `P` is a terminal normalizer for the construction
when it is the normalizer at some stabilization stage.

This relation does not assert that such a finite stage exists. -/
def IsTerminalUnipotentNormalizer
    (isUnipotentElement : G → Prop) (U P : Subgroup G) : Prop :=
  ∃ n : ℕ,
    IsUnipotentNormalizerStabilizationStage isUnipotentElement U n ∧
      P = unipotentNormalizerAt isUnipotentElement U n

end LeanCategories.AlgebraicGeometry
