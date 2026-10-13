/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Constructions

/-!
# Euclidean neighborhood retracts

Definition-level realization of Hatcher FC07-CA-U011.  An ENR is a space that
embeds in some finite-dimensional Euclidean space with image a retract of an
open neighborhood.  Only this defining predicate is recorded here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open Set

universe u v

/-- A subset `S` of `Y` is a retract of an open neighborhood when there is an
open set `U` containing `S` and a continuous retraction `U → S`. -/
def IsOpenNeighborhoodRetract {Y : Type v} [TopologicalSpace Y] (S : Set Y) : Prop :=
  ∃ (U : Set Y) (hU : IsOpen U) (hSU : S ⊆ U) (r : ContinuousMap U S),
    ∀ s : S, (r ⟨s.1, hSU s.2⟩ : Y) = s.1

/-- Hatcher's Euclidean-neighborhood-retract predicate: `X` embeds in some
`ℝ^n` as a retract of an open neighborhood of its image. -/
def IsEuclideanNeighborhoodRetract (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (n : ℕ) (e : X → EuclideanSpace ℝ (Fin n)),
    Topology.IsEmbedding e ∧ IsOpenNeighborhoodRetract (range e)

end LeanCategories.Topology
