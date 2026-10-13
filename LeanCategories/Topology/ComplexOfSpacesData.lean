/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.DeltaComplex
public import LeanCategories.Topology.MappingCylinderData
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Complexes of spaces and iterated mapping cylinders

Definition-level realization of Hatcher FC07-C04-U142.

For one simplex, Hatcher's string

`X₀ → X₁ → ··· → Xₙ`

is recorded as raw spaces and maps between ordered vertices.  Identity,
composition, and compatibility across faces are separate source predicates,
not proof-valued constructor fields.  The iterated mapping cylinder is built
exactly as in the source: for `n+1`, project the previous cylinder to `Xₙ`,
compose with the last arrow, and take the ordinary mapping cylinder of that
composite.

The later face-restriction and total-realization data are recorded below at
their source level.  Statements that the recursively selected face maps have
the expected embeddings, that all higher face identifications are coherent,
or that the resulting realization has a homotopy-colimit universal property
are result-layer assertions and are not proved in Sweep III.
-/

@[expose] public noncomputable section

open _root_.CategoryTheory
open scoped _root_.CategoryTheory

namespace LeanCategories.Topology

universe u v

/-- Raw space-and-map data on the ordered vertices of one simplex.

Maps are recorded for every ordered pair of vertices so that Hatcher's
commutativity requirement can be stated separately, rather than embedded as
proof fields in the data constructor. -/
structure SimplexSpaceDiagramData (n : ℕ) where
  obj : Fin (n + 1) → TopCat.{u}
  map : ∀ (i j : Fin (n + 1)), (i ≤ j) → (obj i ⟶ obj j)

/-- The source condition saying that the raw maps on one simplex form the
commuting diagram required by Hatcher. -/
def IsSimplexSpaceDiagramData {n : ℕ}
    (D : SimplexSpaceDiagramData.{u} n) : Prop :=
  (∀ i, D.map i i le_rfl = 𝟙 (D.obj i)) ∧
    ∀ (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k),
      D.map i k (hij.trans hjk) = D.map i j hij ≫ D.map j k hjk

/-- Forget the last vertex of a raw simplex diagram. -/
def SimplexSpaceDiagramData.init {n : ℕ}
    (D : SimplexSpaceDiagramData.{u} (n + 1)) :
    SimplexSpaceDiagramData.{u} n where
  obj i := D.obj i.castSucc
  map i j hij :=
    D.map i.castSucc j.castSucc (by
      simpa only [Fin.le_iff_val_le_val, Fin.val_castSucc] using hij)

/-- Delete the vertex `r` from a raw simplex diagram. -/
def SimplexSpaceDiagramData.face {n : ℕ}
    (D : SimplexSpaceDiagramData.{u} (n + 1))
    (r : Fin (n + 2)) :
    SimplexSpaceDiagramData.{u} n where
  obj i := D.obj (r.succAbove i)
  map i j hij :=
    D.map (r.succAbove i) (r.succAbove j)
      ((Fin.succAbove_le_succAbove_iff).2 hij)

/-- The map between consecutive vertices used by the iterated-cylinder
recursion. -/
def SimplexSpaceDiagramData.adjacentMap {n : ℕ}
    (D : SimplexSpaceDiagramData.{u} (n + 1))
    (i : Fin (n + 1)) :
    D.obj i.castSucc ⟶ D.obj i.succ :=
  D.map i.castSucc i.succ (by
    simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ]
    exact Nat.le_succ _)

/-- The final object of a raw simplex diagram. -/
abbrev SimplexSpaceDiagramData.right {n : ℕ}
    (D : SimplexSpaceDiagramData.{u} n) : TopCat.{u} :=
  D.obj (Fin.last n)

/-- One stage of Hatcher's recursive iterated mapping-cylinder construction,
bundled with the canonical projection onto its target end. -/
structure IteratedMappingCylinderData {n : ℕ}
    (F : SimplexSpaceDiagramData.{u} n) where
  carrier : TopCat.{u}
  projectionToTarget : carrier ⟶ F.right
  targetInclusion : F.right ⟶ carrier

/-- Hatcher's iterated mapping cylinder of a composable string
`X₀ → ··· → Xₙ`, together with its canonical projection to `Xₙ`.

At length zero this is just `X₀`.  At a successor, it is the mapping
cylinder of the composite of the previous target projection with the last
map in the string. -/
def iteratedMappingCylinderData :
    {n : ℕ} →
      (F : SimplexSpaceDiagramData.{u} n) →
        IteratedMappingCylinderData F
  | 0, F =>
      { carrier := F.right
        projectionToTarget := 𝟙 _
        targetInclusion := 𝟙 _ }
  | n + 1, F =>
      let P := iteratedMappingCylinderData F.init
      let lastMap : F.init.right ⟶ F.right :=
        F.adjacentMap (Fin.last n)
      let attach : P.carrier ⟶ F.right :=
        P.projectionToTarget ≫ lastMap
      { carrier := TopCat.of (MappingCylinder attach.hom)
        projectionToTarget :=
          TopCat.ofHom (mappingCylinderProjection attach.hom)
        targetInclusion :=
          TopCat.ofHom (mappingCylinderTargetInclusion attach.hom) }

/-- Underlying topological space of Hatcher's iterated mapping cylinder. -/
abbrev IteratedMappingCylinder {n : ℕ}
    (F : SimplexSpaceDiagramData.{u} n) : TopCat.{u} :=
  (iteratedMappingCylinderData F).carrier

/-- The canonical projection of an iterated mapping cylinder onto the final
space in its defining string. -/
def iteratedMappingCylinderTargetProjection {n : ℕ}
    (F : SimplexSpaceDiagramData.{u} n) :
    IteratedMappingCylinder F ⟶ F.right :=
  (iteratedMappingCylinderData F).projectionToTarget

/-- The canonical inclusion of the final space of the string as the target end
of its iterated mapping cylinder. -/
def iteratedMappingCylinderTargetInclusion {n : ℕ}
    (F : SimplexSpaceDiagramData.{u} n) :
    F.right ⟶ IteratedMappingCylinder F :=
  (iteratedMappingCylinderData F).targetInclusion

/-- A chosen codimension-one face simplex from the face data already carried
by a `DeltaComplex`. -/
def deltaComplexFaceSimplex {B : Type u} [TopologicalSpace B]
    (Γ : DeltaComplex B) (n : ℕ) (s : Γ.Simplex (n + 1))
    (i : Fin (n + 2)) : Γ.Simplex n :=
  Classical.choose (Γ.face n s i)

/-- Raw data of a complex of spaces over a Delta-complex.

Each simplex carries its ordered space diagram.  The assertions that these
diagrams commute and that the diagram on a face agrees with the restriction
of the larger diagram are deliberately kept in `IsComplexOfSpacesData`. -/
structure ComplexOfSpacesData {B : Type u} [TopologicalSpace B]
    (Γ : DeltaComplex B) where
  simplexDiagram :
    ∀ n : ℕ, Γ.Simplex n → SimplexSpaceDiagramData.{u} n

/-- Exact source predicate for Hatcher's complex-of-spaces condition:
every simplex diagram commutes, and the data restrict literally to the chosen
Delta-complex face diagrams. -/
def IsComplexOfSpacesData {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} (D : ComplexOfSpacesData Γ) : Prop :=
  (∀ (n : ℕ) (s : Γ.Simplex n),
      IsSimplexSpaceDiagramData (D.simplexDiagram n s)) ∧
    ∀ (n : ℕ) (s : Γ.Simplex (n + 1)) (i : Fin (n + 2)),
      D.simplexDiagram n (deltaComplexFaceSimplex Γ n s i) =
        (D.simplexDiagram (n + 1) s).face i

/-- The iterated mapping cylinder attached to one simplex of a complex of
spaces. -/
abbrev complexOfSpacesSimplexCylinder {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} (D : ComplexOfSpacesData Γ)
    (n : ℕ) (s : Γ.Simplex n) : TopCat.{u} :=
  IteratedMappingCylinder (D.simplexDiagram n s)

/-- Raw realization data attached to a complex of spaces.

Hatcher's construction supplies a projection of each iterated cylinder to its
standard simplex and a restriction map from the cylinder over each face into
the cylinder over the containing simplex.  These functions are recorded as
data.  Their continuity, embedding behavior, and compatibility with the
simplex projections are source conditions in
`IsComplexOfSpacesRealizationData`, not constructor proofs. -/
structure ComplexOfSpacesRealizationData {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} (D : ComplexOfSpacesData Γ) where
  simplexProjection :
    ∀ (n : ℕ) (s : Γ.Simplex n),
      complexOfSpacesSimplexCylinder D n s →
        stdSimplex ℝ (Fin (n + 1))
  faceMap :
    ∀ (n : ℕ) (s : Γ.Simplex (n + 1)) (i : Fin (n + 2)),
      complexOfSpacesSimplexCylinder D n
          (deltaComplexFaceSimplex Γ n s i) →
        complexOfSpacesSimplexCylinder D (n + 1) s

/-- Source conditions on the raw realization functions.

This predicate records, but does not prove in Sweep III, that the simplex
projections and face maps are continuous, that each face map is an embedding,
and that it lies over the corresponding standard-simplex face. -/
def IsComplexOfSpacesRealizationData {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} {D : ComplexOfSpacesData Γ}
    (R : ComplexOfSpacesRealizationData D) : Prop :=
  IsComplexOfSpacesData D ∧
    (∀ (n : ℕ) (s : Γ.Simplex n),
      Continuous (R.simplexProjection n s)) ∧
    (∀ (n : ℕ) (s : Γ.Simplex (n + 1)) (i : Fin (n + 2)),
      Continuous (R.faceMap n s i) ∧
        Topology.IsEmbedding (R.faceMap n s i) ∧
        ∀ x,
          R.simplexProjection (n + 1) s (R.faceMap n s i x) =
            stdSimplexFaceInclusion i
              (R.simplexProjection n
                (deltaComplexFaceSimplex Γ n s i) x))

/-- Disjoint union of all simplexwise iterated mapping cylinders before the
face identifications.  The dimension and simplex tags carry the discrete
topology, so the sigma topology is the coproduct topology on the pieces. -/
abbrev ComplexOfSpacesRealizationPre {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} (D : ComplexOfSpacesData Γ) :=
  Σ n : WithDiscreteTopology ℕ,
    Σ s : WithDiscreteTopology (Γ.Simplex n.ofTopology),
      complexOfSpacesSimplexCylinder D n.ofTopology s.ofTopology

/-- The generating identifications that glue each simplexwise iterated
mapping cylinder to the cylinder over a containing simplex along a face. -/
inductive ComplexOfSpacesRealizationGlue {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} (D : ComplexOfSpacesData Γ)
    (R : ComplexOfSpacesRealizationData D) :
    ComplexOfSpacesRealizationPre D →
      ComplexOfSpacesRealizationPre D → Prop
  | face (n : ℕ) (s : Γ.Simplex (n + 1)) (i : Fin (n + 2))
      (x : complexOfSpacesSimplexCylinder D n
        (deltaComplexFaceSimplex Γ n s i)) :
      ComplexOfSpacesRealizationGlue D R
        ⟨WithTopology.toTopology (⊥ : TopologicalSpace ℕ) n,
          WithTopology.toTopology
            (⊥ : TopologicalSpace (Γ.Simplex n))
            (deltaComplexFaceSimplex Γ n s i),
          x⟩
        ⟨WithTopology.toTopology (⊥ : TopologicalSpace ℕ) (n + 1),
          WithTopology.toTopology
            (⊥ : TopologicalSpace (Γ.Simplex (n + 1))) s,
          R.faceMap n s i x⟩

/-- Equivalence relation generated by all face identifications. -/
def complexOfSpacesRealizationSetoid {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} (D : ComplexOfSpacesData Γ)
    (R : ComplexOfSpacesRealizationData D) :
    Setoid (ComplexOfSpacesRealizationPre D) :=
  Relation.EqvGen.setoid (ComplexOfSpacesRealizationGlue D R)

/-- Hatcher's total realization `ΔX` as the quotient obtained by gluing the
simplexwise iterated mapping cylinders along all face maps. -/
abbrev ComplexOfSpacesRealization {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} (D : ComplexOfSpacesData Γ)
    (R : ComplexOfSpacesRealizationData D) :=
  Quotient (complexOfSpacesRealizationSetoid D R)

/-- The prequotient formula for Hatcher's canonical projection
`ΔX → Γ`: first project to the standard simplex, then use the
Delta-complex characteristic map.

Descent of this formula through the face-gluing quotient is a
well-definedness result and is intentionally not proved in Sweep III. -/
def complexOfSpacesRealizationProjectionPre {B : Type u} [TopologicalSpace B]
    {Γ : DeltaComplex B} {D : ComplexOfSpacesData Γ}
    (R : ComplexOfSpacesRealizationData D) :
    ComplexOfSpacesRealizationPre D → B
  | ⟨n, s, x⟩ =>
      Γ.characteristic n.ofTopology s.ofTopology
        (R.simplexProjection n.ofTopology s.ofTopology x)

end LeanCategories.Topology
