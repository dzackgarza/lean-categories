/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.MilnorFiberIntersectionData
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Homotopy.Path

/-!
# Geometric monodromy of the Milnor fibre

Definition-level realization of Peters--Sterk FC11-C18-U026.

The source monodromy is not an arbitrary automorphism of middle homology. It
is induced by moving the actual Milnor fibre once counterclockwise around the
origin in the punctured parameter disk.

Mathlib has path monodromy for covering maps, but no general parallel
transport construction for the higher-dimensional locally trivial Milnor
fibration. To keep Sweep III proof-free without replacing the source object,
this file records the exact geometric graph of the missing transport:

* the base path is the standard positive loop t ↦ t_* exp(2 pi i t);
* a candidate endpoint map of the actual Milnor fibre is accepted only when
  it is the endpoint of a continuous family of points lying in the
  corresponding moving level sets.

Sweep III therefore constructs the carrier of positive-loop data and, over
each such loop, the carrier of endpoint maps satisfying the geometric
transport graph. Native singular homology functoriality then supplies the
middle-homology operator for every certified transport datum.

Existence of the lifted family homotopy, independence of transport choices,
invertibility, preservation of the Milnor pairing, and the usual fibration
theorems are result-layer content and are not proved in Sweep III.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace LeanCategories.Topology

/-- Candidate loop in the punctured parameter disk based at the chosen
Milnor-fibre parameter. -/
abbrev MilnorPositiveLoopCandidateData {r : ℝ}
    (t : milnorPuncturedDiskData r) :=
  Path t t

/-- Exact graph for the once-counterclockwise loop around the origin. -/
def IsMilnorPositiveLoopData {r : ℝ}
    (t : milnorPuncturedDiskData r)
    (gamma : MilnorPositiveLoopCandidateData t) : Prop :=
  ∀ s : I,
    (gamma s : ℂ) =
      t.1 * Complex.exp ((2 * Real.pi * (s : ℝ) : ℂ) * Complex.I)

/-- The carrier of paths having the source's exact positive-loop formula.
No path is selected before continuity and punctured-disk membership of the
formula are established. -/
def MilnorPositiveLoopData {r : ℝ}
    (t : milnorPuncturedDiskData r) :=
  {gamma : MilnorPositiveLoopCandidateData t // IsMilnorPositiveLoopData t gamma}

/-- Candidate endpoint self-map of the actual Milnor fibre. -/
abbrev MilnorGeometricMonodromyMapCandidateData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) :=
  C(MilnorFiberData f eta t, MilnorFiberData f eta t)

/-- Exact geometric transport graph for a candidate endpoint map.

The witness H is a continuous family of ambient points parameterized by
the positive loop and the starting fibre. At time s it lies inside the
chosen Milnor neighbourhood and on the level set over gamma(s); at time
zero it is the original fibre point, and at time one it is the candidate
endpoint map. No transport-existence theorem is asserted here. -/
def IsMilnorGeometricMonodromyMapData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r)
    (gamma : MilnorPositiveLoopData t)
    (g : MilnorGeometricMonodromyMapCandidateData f eta t) : Prop :=
  ∃ H : C(I × MilnorFiberData f eta t, MilnorCoordinateSpaceData n),
    (∀ s z,
      ‖H (s, z)‖ ^ 2 < eta ∧
        f (H (s, z)) = (gamma.1 s : ℂ)) ∧
    (∀ z, H (0, z) = z.1) ∧
    (∀ z, H (1, z) = (g z).1)

/-- The carrier of geometric endpoint maps obtained by transport along a
certified positive loop.  No endpoint map is selected before transport
existence is proved. -/
def MilnorGeometricMonodromyMapData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r)
    (gamma : MilnorPositiveLoopData t) :=
  {g : MilnorGeometricMonodromyMapCandidateData f eta t //
    IsMilnorGeometricMonodromyMapData f eta t gamma g}

/-- Peters--Sterk's Milnor monodromy operator on integral middle homology,
induced functorially by the geometric endpoint map above. -/
noncomputable def milnorMonodromyOperatorData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r)
    (gamma : MilnorPositiveLoopData t)
    (g : MilnorGeometricMonodromyMapData f eta t gamma) :
    milnorIntegralMiddleHomologyData f eta t ⟶
      milnorIntegralMiddleHomologyData f eta t :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom g.1)

/-- The carrier of all middle-homology operators produced by source-valid
positive-loop transports.  Transport existence and independence later show
that this carrier contains the canonical monodromy operator. -/
def milnorMonodromyOperatorCarrierData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) :
    Set (milnorIntegralMiddleHomologyData f eta t ⟶
      milnorIntegralMiddleHomologyData f eta t) :=
  {T | ∃ (gamma : MilnorPositiveLoopData t)
      (g : MilnorGeometricMonodromyMapData f eta t gamma),
    T = milnorMonodromyOperatorData f eta t gamma g}

end LeanCategories.Topology
