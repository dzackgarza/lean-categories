/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.HypersurfaceUnfoldingRegularFamilyData
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Path

/-!
# Local monodromy of a hypersurface unfolding

Definition-level realization of Peters--Sterk FC11-C18-U035.

The source local monodromy group is the image of the fundamental group of
the discriminant complement acting on the integral middle homology of a
reference Milnor fibre.

The actual discriminant-complement family, reference fibre and native middle
homology are already constructed in HypersurfaceUnfoldingRegularFamilyData.
Mathlib has canonical monodromy for covering maps but no path transport for a
general higher-dimensional locally trivial fibre bundle. As in the preceding
Milnor-loop construction, this file records the exact geometric graph instead
of accepting a representation as input.

For each fundamental-group element, a candidate endpoint self-map of the
actual reference fibre qualifies only when a representative loop admits a
continuous family of points through the corresponding moving zero fibres,
starting at the given point and ending at that self-map. Native singular
homology functoriality then produces the action value. The local monodromy
carrier is literally the range of these values.

Existence and independence of geometric transport, the group-action law,
invertibility, preservation of the intersection pairing, and the statement
that this carrier is a subgroup of the appropriate automorphism/isometry
group are result-layer content and are not proved in Sweep III.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

namespace LeanCategories.Topology

/-- The discriminant-complement base used by the local monodromy
construction. -/
abbrev HypersurfaceUnfoldingMonodromyBaseData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) :=
  hypersurfaceUnfoldingRegularBaseSetData f B V U

/-- Candidate endpoint self-map of the actual reference fibre. -/
abbrev HypersurfaceUnfoldingTransportMapCandidateData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m))
    (t : HypersurfaceUnfoldingMonodromyBaseData f B V U) :=
  C(HypersurfaceUnfoldingReferenceFiberData f B V U t,
    HypersurfaceUnfoldingReferenceFiberData f B V U t)

/-- Exact geometric transport graph for one fundamental-group element.

The path gamma represents the specified element. The witness H is a
continuous family in the ambient coordinate space which remains inside the
chosen unfolding neighbourhood and on the zero fibre over gamma(s). It
starts at the original reference-fibre point and ends at the candidate map.
-/
def IsHypersurfaceUnfoldingTransportMapData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m))
    (t : HypersurfaceUnfoldingMonodromyBaseData f B V U)
    (loop : FundamentalGroup
      (HypersurfaceUnfoldingMonodromyBaseData f B V U) t)
    (g : HypersurfaceUnfoldingTransportMapCandidateData f B V U t) : Prop :=
  ∃ gamma : Path t t,
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma) = loop ∧
    ∃ H : C(I × HypersurfaceUnfoldingReferenceFiberData f B V U t,
        MilnorCoordinateSpaceData n),
      (∀ s z,
        (H (s, z), (gamma s).1) ∈ V ∧
          hypersurfaceUnfoldingFunctionData f B (gamma s).1 (H (s, z)) = 0) ∧
      (∀ z, H (0, z) = z.1) ∧
      (∀ z, H (1, z) = (g z).1)

/-- The carrier of endpoint self-maps attached to a fundamental-group element
by the exact geometric transport graph.  No endpoint is selected before
transport existence is proved. -/
def HypersurfaceUnfoldingTransportMapData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m))
    (t : HypersurfaceUnfoldingMonodromyBaseData f B V U)
    (loop : FundamentalGroup
      (HypersurfaceUnfoldingMonodromyBaseData f B V U) t) :=
  {g : HypersurfaceUnfoldingTransportMapCandidateData f B V U t //
    IsHypersurfaceUnfoldingTransportMapData f B V U t loop g}

/-- The middle-homology endomorphism induced by geometric transport along a
fundamental-group element. -/
noncomputable def hypersurfaceUnfoldingMonodromyOperatorData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m))
    (t : HypersurfaceUnfoldingMonodromyBaseData f B V U)
    (loop : FundamentalGroup
      (HypersurfaceUnfoldingMonodromyBaseData f B V U) t)
    (g : HypersurfaceUnfoldingTransportMapData f B V U t loop) :
    hypersurfaceUnfoldingReferenceHomologyData f B V U t ⟶
      hypersurfaceUnfoldingReferenceHomologyData f B V U t :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom
        g.1)

/-- Peters--Sterk's local monodromy-group carrier: the image of the
fundamental group on the actual reference-fibre middle homology.

The result that this set is a group of automorphisms/isometries follows from
transport functoriality and invertibility and is deliberately deferred. -/
noncomputable def localMonodromyGroupCarrierData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m))
    (t : HypersurfaceUnfoldingMonodromyBaseData f B V U) :
    Set (hypersurfaceUnfoldingReferenceHomologyData f B V U t ⟶
      hypersurfaceUnfoldingReferenceHomologyData f B V U t) :=
  {T | ∃ (loop : FundamentalGroup
        (HypersurfaceUnfoldingMonodromyBaseData f B V U) t)
      (g : HypersurfaceUnfoldingTransportMapData f B V U t loop),
    T = hypersurfaceUnfoldingMonodromyOperatorData f B V U t loop g}

end LeanCategories.Topology
