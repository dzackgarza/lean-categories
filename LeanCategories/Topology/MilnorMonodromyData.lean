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

The source-named endpoint map is selected from that graph and native singular
homology functoriality supplies the middle-homology operator.

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

/-- The source positive loop, selected by its exact complex-exponential
parameterization. Continuity and punctured-disk membership are properties of
the path candidate; their existence for this formula is result-layer
well-definedness rather than a Sweep-III proof obligation. -/
noncomputable def milnorPositiveLoopData {r : ℝ}
    (t : milnorPuncturedDiskData r) :
    MilnorPositiveLoopCandidateData t :=
  letI : Nonempty (MilnorPositiveLoopCandidateData t) := ⟨Path.refl t⟩
  Classical.epsilon (IsMilnorPositiveLoopData t)

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
    (g : MilnorGeometricMonodromyMapCandidateData f eta t) : Prop :=
  let gamma := milnorPositiveLoopData t
  ∃ H : C(I × MilnorFiberData f eta t, MilnorCoordinateSpaceData n),
    (∀ s z,
      ‖H (s, z)‖ ^ 2 < eta ∧
        f (H (s, z)) = (gamma s : ℂ)) ∧
    (∀ z, H (0, z) = z.1) ∧
    (∀ z, H (1, z) = (g z).1)

/-- The geometric endpoint self-map obtained by transporting the Milnor fibre
once counterclockwise around the origin. -/
noncomputable def milnorGeometricMonodromyMapData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) :
    MilnorGeometricMonodromyMapCandidateData f eta t :=
  letI : Nonempty (MilnorGeometricMonodromyMapCandidateData f eta t) :=
    ⟨ContinuousMap.id _⟩
  Classical.epsilon (IsMilnorGeometricMonodromyMapData f eta t)

/-- Peters--Sterk's Milnor monodromy operator on integral middle homology,
induced functorially by the geometric endpoint map above. -/
noncomputable def milnorMonodromyOperatorData {n : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ) (eta : ℝ) {r : ℝ}
    (t : milnorPuncturedDiskData r) :
    milnorIntegralMiddleHomologyData f eta t ⟶
      milnorIntegralMiddleHomologyData f eta t :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom (milnorGeometricMonodromyMapData f eta t))

end LeanCategories.Topology
