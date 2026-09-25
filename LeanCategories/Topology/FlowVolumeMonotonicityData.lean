/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Volume monotonicity of flows

Definition-level realization of Lee FC08-C16-U043.

Lee's five notions use only the volume of compact regular domains under the
time-t maps of a smooth flow.  The geometric construction of that volume and
the proof that a flow image is again a compact regular domain are supplied by
their respective owners; no normalization or invariance theorem is proved here.
-/

@[expose] public section

namespace LeanCategories.Topology

/-- A flow is volume-preserving when every compact regular domain keeps the
same volume at every time for which the flow map is defined on that domain. -/
def IsVolumePreservingFlow
    {Flow CompactRegularDomain : Type*}
    (volume : CompactRegularDomain → ℝ)
    (flowImage : Flow → ℝ → CompactRegularDomain → CompactRegularDomain)
    (definedOn : Flow → ℝ → CompactRegularDomain → Prop)
    (θ : Flow) : Prop :=
  ∀ D t, definedOn θ t D → volume (flowImage θ t D) = volume D

/-- The volume of every compact regular domain is strictly increasing along
the times on which the flow is defined on that domain. -/
def IsVolumeIncreasingFlow
    {Flow CompactRegularDomain : Type*}
    (volume : CompactRegularDomain → ℝ)
    (flowImage : Flow → ℝ → CompactRegularDomain → CompactRegularDomain)
    (definedOn : Flow → ℝ → CompactRegularDomain → Prop)
    (θ : Flow) : Prop :=
  ∀ D s t, s < t → definedOn θ s D → definedOn θ t D →
    volume (flowImage θ s D) < volume (flowImage θ t D)

/-- The volume of every compact regular domain is strictly decreasing along
the times on which the flow is defined on that domain. -/
def IsVolumeDecreasingFlow
    {Flow CompactRegularDomain : Type*}
    (volume : CompactRegularDomain → ℝ)
    (flowImage : Flow → ℝ → CompactRegularDomain → CompactRegularDomain)
    (definedOn : Flow → ℝ → CompactRegularDomain → Prop)
    (θ : Flow) : Prop :=
  ∀ D s t, s < t → definedOn θ s D → definedOn θ t D →
    volume (flowImage θ t D) < volume (flowImage θ s D)

/-- The volume of every compact regular domain is nonincreasing along the
times on which the flow is defined on that domain. -/
def IsVolumeNonincreasingFlow
    {Flow CompactRegularDomain : Type*}
    (volume : CompactRegularDomain → ℝ)
    (flowImage : Flow → ℝ → CompactRegularDomain → CompactRegularDomain)
    (definedOn : Flow → ℝ → CompactRegularDomain → Prop)
    (θ : Flow) : Prop :=
  ∀ D s t, s < t → definedOn θ s D → definedOn θ t D →
    volume (flowImage θ t D) ≤ volume (flowImage θ s D)

/-- The volume of every compact regular domain is nondecreasing along the
times on which the flow is defined on that domain. -/
def IsVolumeNondecreasingFlow
    {Flow CompactRegularDomain : Type*}
    (volume : CompactRegularDomain → ℝ)
    (flowImage : Flow → ℝ → CompactRegularDomain → CompactRegularDomain)
    (definedOn : Flow → ℝ → CompactRegularDomain → Prop)
    (θ : Flow) : Prop :=
  ∀ D s t, s < t → definedOn θ s D → definedOn θ t D →
    volume (flowImage θ s D) ≤ volume (flowImage θ t D)

end LeanCategories.Topology
