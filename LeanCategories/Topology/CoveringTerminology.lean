/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open Set

universe u v w

variable {E : Type u} {E' : Type v} {B : Type w}
variable [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]

/-- Equivalence of covering maps over a common base (FC02-C13-U001). -/
def CoveringEquivalent (p : E → B) (q : E' → B) : Prop :=
  ∃ h : E ≃ₜ E', p = q ∘ h

/-- Covering transformations of a map, bundled as a subgroup of self-homeomorphisms
(FC02-C13-U014). -/
def deckGroup (p : E → B) : Subgroup (E ≃ₜ E) where
  carrier := {h | p ∘ h = p}
  one_mem' := by
    ext x
    rfl
  mul_mem' := by
    intro h k hh hk
    ext x
    change p ((h * k) x) = p x
    rw [Homeomorph.mul_apply]
    exact (congrFun hh (k x)).trans (congrFun hk x)
  inv_mem' := by
    intro h hh
    ext x
    change p (h⁻¹ x) = p x
    have hhx := congrFun hh (h⁻¹ x)
    simpa using hhx.symm

/-- Fiber of a map over a basepoint. -/
abbrev coveringFiber (p : E → B) (b : B) := p ⁻¹' {b}

/-- Evaluation of a covering transformation at a chosen point (definition-level part of
FC02-C13-U016). -/
def deckEvaluation (p : E → B) (e₀ : E) : deckGroup p → coveringFiber p (p e₀) :=
  fun h => ⟨h.1 e₀, by
    change p (h.1 e₀) = p e₀
    exact congrFun h.2 e₀⟩

/-- Munkres regularity at a chosen point: the image of the induced fundamental-group map is
normal (FC02-C13-U021). -/
def IsRegularCoveringAt (p : E → B) (hp : IsCoveringMap p) (e₀ : E) : Prop :=
  (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range.Normal

/-- Semilocal simple connectivity at a point, expressed by a neighborhood whose inclusion has
trivial fundamental-group image (FC02-C13-U029). -/
def SemilocallySimplyConnectedAt (b : B) : Prop :=
  ∃ (U : Set B) (hb : b ∈ U), U ∈ nhds b ∧
    (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ (⟨b, hb⟩ : U)).range = ⊥

/-- A space is semilocally simply connected when it is so at every point. -/
def SemilocallySimplyConnected (B : Type*) [TopologicalSpace B] : Prop :=
  ∀ b : B, SemilocallySimplyConnectedAt b

end LeanCategories.Topology
