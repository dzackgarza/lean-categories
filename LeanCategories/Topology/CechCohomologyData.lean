/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sets.OpenCover

/-!
# Cech cohomology definition data

Definition-level realization of Hatcher FC07-C03-U072.

For every open cover U of X, Hatcher forms the nerve N(U). A refinement
choice gives a simplicial map from the finer nerve to the coarser nerve and
hence a cohomology map in the other direction. Cech cohomology is the direct
limit of these groups over refinements.

The obstruction to a proof-free direct-system constructor is coherence:
different containment choices must induce the same cohomology map, and these
maps must compose. Those are result statements. This file therefore records
the concrete nerve-face predicate, refinement choices, the ordinary
nerve-cohomology stages/maps supplied by the preceding cohomology layer, and
then characterizes the direct limit by its exact categorical universal
property. The Cech group is selected by Classical.epsilon.

No choice-independence, directedness, transition coherence, or colimit
existence theorem is proved in Sweep III.
-/

@[expose] public noncomputable section

open CategoryTheory
open TopologicalSpace

namespace LeanCategories.Topology

universe u v

/-- An open cover represented canonically as a set of open subsets whose
supremum is the whole space. -/
structure CechOpenCoverData (X : Type u) [TopologicalSpace X] where
  opens : Set (Opens X)
  covers : sSup opens = ⊤

/-- Vertices of the nerve of an open cover. -/
abbrev CechNerveVertexData
    {X : Type u} [TopologicalSpace X] (U : CechOpenCoverData X) :=
  U.opens

/-- Face predicate for the nerve N(U): a finite family of cover elements is a
simplex exactly when its total intersection is nonempty. -/
def CechNerveFaceData
    {X : Type u} [TopologicalSpace X] (U : CechOpenCoverData X)
    (s : Finset (CechNerveVertexData U)) : Prop :=
  ∃ x : X, ∀ V, V ∈ s → x ∈ (V.1 : Set X)

/-- The relation saying that V refines U. -/
def CechRefinesData
    {X : Type u} [TopologicalSpace X]
    (V U : CechOpenCoverData X) : Prop :=
  ∀ W : CechNerveVertexData V,
    ∃ Z : CechNerveVertexData U, W.1 ≤ Z.1

/-- A concrete containment choice witnessing a refinement. Such a choice
induces the usual simplicial map N(V) to N(U). -/
structure CechRefinementChoiceData
    {X : Type u} [TopologicalSpace X]
    (V U : CechOpenCoverData X) where
  toCoarse : CechNerveVertexData V → CechNerveVertexData U
  contained : ∀ W, W.1 ≤ (toCoarse W).1

/-- The already-defined ordinary cohomology of the cover nerves in degree i,
together with the map induced by each concrete refinement choice.

The parameter G is the coefficient group. The ordinary cohomology layer owns
the construction of each stage and each map; this record deliberately carries
no coherence or choice-independence proof. -/
structure CechNerveCohomologyPresentationData
    (X : Type u) [TopologicalSpace X]
    (G : Type v) [AddCommGroup G] (i : ℕ) where
  stage : CechOpenCoverData X → AddCommGrpCat.{max u v}
  inducedByChoice :
    {U V : CechOpenCoverData X} →
      (CechRefinementChoiceData V U → (stage U ⟶ stage V))

/-- A refinement-induced cohomology map is one arising from some containment
choice. -/
def IsCechRefinementCohomologyMapData
    {X : Type u} [TopologicalSpace X]
    {G : Type v} [AddCommGroup G] {i : ℕ}
    (D : CechNerveCohomologyPresentationData X G i)
    (V U : CechOpenCoverData X)
    (f : D.stage U ⟶ D.stage V) : Prop :=
  ∃ c : CechRefinementChoiceData V U, f = D.inducedByChoice c

/-- The cohomology map attached to a refinement, selected without proving
independence of the containment choice. -/
def cechRefinementCohomologyMapData
    {X : Type u} [TopologicalSpace X]
    {G : Type v} [AddCommGroup G] {i : ℕ}
    (D : CechNerveCohomologyPresentationData X G i)
    (V U : CechOpenCoverData X) :
    D.stage U ⟶ D.stage V :=
  Classical.epsilon
    (IsCechRefinementCohomologyMapData D V U)

/-- Candidate direct-limit data: an abelian group and one structure map from
every nerve-cohomology stage. -/
structure CechCohomologyCandidateData
    {X : Type u} [TopologicalSpace X]
    {G : Type v} [AddCommGroup G] {i : ℕ}
    (D : CechNerveCohomologyPresentationData X G i) where
  carrier : AddCommGrpCat.{max u v}
  ofCover : (U : CechOpenCoverData X) → D.stage U ⟶ carrier

/-- Ambient candidate data are always available, so the source colimit can be
named without supplying its existence theorem as a constructor argument. -/
instance
    {X : Type u} [TopologicalSpace X]
    {G : Type v} [AddCommGroup G] {i : ℕ}
    (D : CechNerveCohomologyPresentationData X G i) :
    Nonempty (CechCohomologyCandidateData D) :=
  ⟨⟨AddCommGrpCat.of (ULift.{max u v} ℤ), fun _ => 0⟩⟩

/-- Exact direct-limit universal-property specification for Hatcher's Cech
cohomology group.

The first clause says the stage maps identify refinement images. The second is
the ordinary universal property for every compatible family of maps out of
the nerve-cohomology stages. -/
def IsCechCohomologyData
    {X : Type u} [TopologicalSpace X]
    {G : Type v} [AddCommGroup G] {i : ℕ}
    (D : CechNerveCohomologyPresentationData X G i)
    (C : CechCohomologyCandidateData D) : Prop :=
  (∀ (U V : CechOpenCoverData X),
      CechRefinesData V U →
        cechRefinementCohomologyMapData D V U ≫ C.ofCover V =
          C.ofCover U) ∧
    ∀ (A : AddCommGrpCat.{max u v})
      (f : (U : CechOpenCoverData X) → D.stage U ⟶ A),
      (∀ (U V : CechOpenCoverData X),
        CechRefinesData V U →
          cechRefinementCohomologyMapData D V U ≫ f V = f U) →
      ∃! g : C.carrier ⟶ A,
        ∀ U : CechOpenCoverData X, C.ofCover U ≫ g = f U

/-- Hatcher's Cech cohomology direct-limit presentation, selected from the
exact universal property. -/
def cechCohomologyCandidateData
    {X : Type u} [TopologicalSpace X]
    {G : Type v} [AddCommGroup G] {i : ℕ}
    (D : CechNerveCohomologyPresentationData X G i) :
    CechCohomologyCandidateData D :=
  Classical.epsilon (IsCechCohomologyData D)

/-- The source-facing Cech cohomology group. -/
abbrev CechCohomologyData
    {X : Type u} [TopologicalSpace X]
    {G : Type v} [AddCommGroup G] {i : ℕ}
    (D : CechNerveCohomologyPresentationData X G i) :
    AddCommGrpCat.{max u v} :=
  (cechCohomologyCandidateData D).carrier

end LeanCategories.Topology
