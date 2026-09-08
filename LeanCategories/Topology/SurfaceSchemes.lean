/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Polygon.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Ordered
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open Set

/-- A filled planar polygonal region together with its cyclic polygonal boundary. -/
structure PolygonalRegion (n : ℕ) where
  carrier : Set ℂ
  polygon : Polygon ℂ n
  nondegenerate : polygon.HasNondegenerateEdges
  boundary_subset : polygon.boundary ℝ ⊆ carrier

namespace PolygonalRegion

/-- The union of the successive polygon edges. -/
def boundary {n : ℕ} (P : PolygonalRegion n) : Set ℂ := P.polygon.boundary ℝ

/-- Munkres' `Int P = P - Bd P` convention. -/
def interior {n : ℕ} (P : PolygonalRegion n) : Set ℂ := P.carrier \ P.boundary

end PolygonalRegion

/-- An orientation of a nondegenerate straight line segment. -/
structure OrientedSegment where
  initial : ℂ
  terminal : ℂ
  nondegenerate : initial ≠ terminal

namespace OrientedSegment

/-- The complex affine scaling carrying one oriented segment to another. -/
def scale (e f : OrientedSegment) : ℂ :=
  (f.terminal - f.initial) / (e.terminal - e.initial)

lemma scale_ne_zero (e f : OrientedSegment) : e.scale f ≠ 0 := by
  apply div_ne_zero
  · exact sub_ne_zero.mpr f.nondegenerate.symm
  · exact sub_ne_zero.mpr e.nondegenerate.symm

/-- Munkres' positive linear map, extended uniquely to an affine homeomorphism of the plane. -/
noncomputable def positiveAffineHomeomorph (e f : OrientedSegment) : ℂ ≃ₜ ℂ where
  toFun z := f.initial + e.scale f * (z - e.initial)
  invFun w := e.initial + (e.scale f)⁻¹ * (w - f.initial)
  left_inv z := by
    dsimp
    field_simp [scale_ne_zero]
    ring
  right_inv w := by
    dsimp
    field_simp [scale_ne_zero]
    ring
  continuous_toFun :=
    continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))
  continuous_invFun :=
    continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))

@[simp] theorem positiveAffineHomeomorph_initial (e f : OrientedSegment) :
    e.positiveAffineHomeomorph f e.initial = f.initial := by
  simp [positiveAffineHomeomorph]

@[simp] theorem positiveAffineHomeomorph_terminal (e f : OrientedSegment) :
    e.positiveAffineHomeomorph f e.terminal = f.terminal := by
  change f.initial + e.scale f * (e.terminal - e.initial) = f.terminal
  rw [scale]
  have h : e.terminal - e.initial ≠ 0 := sub_ne_zero.mpr e.nondegenerate.symm
  rw [div_mul_cancel₀ _ h]
  ring

/-- The affine unit-interval parametrization in the chosen orientation. -/
def point (e : OrientedSegment) (t : unitInterval) : ℂ :=
  AffineMap.lineMap e.initial e.terminal (t : ℝ)

end OrientedSegment

/-- Direction of an oriented polygon edge relative to cyclic boundary order. -/
inductive EdgeDirection
  | forward
  | reverse
deriving DecidableEq, Repr

/-- Sign attached to a label in a labelling scheme. -/
inductive OrientationSign
  | pos
  | neg
deriving DecidableEq, Repr

namespace OrientationSign

def flip : OrientationSign → OrientationSign
  | pos => neg
  | neg => pos

@[simp] theorem flip_flip (s : OrientationSign) : s.flip.flip = s := by cases s <;> rfl

end OrientationSign

namespace EdgeDirection

def sign : EdgeDirection → OrientationSign
  | forward => .pos
  | reverse => .neg

end EdgeDirection

namespace PolygonalRegion

/-- The `i`th polygon edge with one of its two orientations. -/
def orientedEdge {n : ℕ} (P : PolygonalRegion n) (i : Fin n)
    (d : EdgeDirection) : OrientedSegment :=
  match d with
  | .forward =>
      ⟨P.polygon i, P.polygon (finRotate n i), P.nondegenerate i⟩
  | .reverse =>
      ⟨P.polygon (finRotate n i), P.polygon i, (P.nondegenerate i).symm⟩

/-- The point with parameter `t` on an oriented polygon edge, bundled in the filled region. -/
def edgePoint {n : ℕ} (P : PolygonalRegion n) (i : Fin n)
    (d : EdgeDirection) (t : unitInterval) : P.carrier := by
  refine ⟨(P.orientedEdge i d).point t, P.boundary_subset ?_⟩
  rw [Polygon.boundary]
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  change AffineMap.lineMap (P.orientedEdge i d).initial
      (P.orientedEdge i d).terminal (t : ℝ) ∈ P.polygon.edgeSet ℝ i
  rw [Polygon.edgeSet]
  cases d with
  | forward => exact ⟨t, t.property, rfl⟩
  | reverse =>
      rw [affineSegment_comm]
      exact ⟨t, t.property, rfl⟩

end PolygonalRegion

/-- A signed edge label, i.e. one letter of a labelling scheme. -/
structure SignedLabel (α : Type*) where
  label : α
  sign : OrientationSign
deriving DecidableEq, Repr

namespace SignedLabel

def inverse {α : Type*} (s : SignedLabel α) : SignedLabel α :=
  ⟨s.label, s.sign.flip⟩

@[simp] theorem inverse_inverse {α : Type*} (s : SignedLabel α) : s.inverse.inverse = s := by
  cases s with | mk a sign => cases sign <;> rfl

end SignedLabel

/-- A labelling scheme is a finite signed word. -/
abbrev LabellingScheme (α : Type*) := List (SignedLabel α)

namespace LabellingScheme

/-- Positions at which a fixed label occurs. -/
def occurrenceSet {α : Type*} (w : LabellingScheme α) (a : α) : Set (Fin w.length) :=
  {i | (w.get i).label = a}

/-- A scheme is proper when every label that occurs appears exactly twice. -/
def IsProper {α : Type*} (w : LabellingScheme α) : Prop :=
  ∀ a, (w.occurrenceSet a).Nonempty → (w.occurrenceSet a).ncard = 2

/-- A proper one-face scheme is of torus type when the two occurrences of every label have
opposite signs. -/
def IsTorusType {α : Type*} (w : LabellingScheme α) : Prop :=
  w.IsProper ∧ ∀ a i j, i ∈ w.occurrenceSet a → j ∈ w.occurrenceSet a → i ≠ j →
    (w.get i).sign ≠ (w.get j).sign

/-- A proper scheme that is not of torus type is of projective type. -/
def IsProjectiveType {α : Type*} (w : LabellingScheme α) : Prop :=
  w.IsProper ∧ ¬ w.IsTorusType

/-- Formal inverse of a signed word. -/
def inverse {α : Type*} (w : LabellingScheme α) : LabellingScheme α :=
  (w.map SignedLabel.inverse).reverse

/-- Relabel every letter by an equivalence of label types. -/
def relabel {α β : Type*} (σ : α ≃ β) (w : LabellingScheme α) : LabellingScheme β :=
  w.map fun s => ⟨σ s.label, s.sign⟩

/-- Reverse the orientation attached to every occurrence of one label. -/
def reverseLabel {α : Type*} [DecidableEq α] (a : α)
    (w : LabellingScheme α) : LabellingScheme α :=
  w.map fun s => if s.label = a then ⟨s.label, s.sign.flip⟩ else s

end LabellingScheme

/-- A finite collection of polygonal labelling schemes. -/
abbrev SchemeCollection (α : Type*) := List (LabellingScheme α)

/-- The source-level elementary operations on collections of labelling schemes. -/
inductive ElementarySchemeMove {α : Type*} [DecidableEq α] :
    SchemeCollection α → SchemeCollection α → Prop
  | cut (pre post : SchemeCollection α) (y₀ y₁ : LabellingScheme α) (c : α)
      (fresh : c ∉ (y₀ ++ y₁).map SignedLabel.label) :
      ElementarySchemeMove
        (pre ++ [y₀ ++ y₁] ++ post)
        (pre ++ [y₀ ++ [⟨c, .neg⟩], [⟨c, .pos⟩] ++ y₁] ++ post)
  | paste (pre post : SchemeCollection α) (y₀ y₁ : LabellingScheme α) (c : α)
      (fresh : c ∉ (y₀ ++ y₁).map SignedLabel.label) :
      ElementarySchemeMove
        (pre ++ [y₀ ++ [⟨c, .neg⟩], [⟨c, .pos⟩] ++ y₁] ++ post)
        (pre ++ [y₀ ++ y₁] ++ post)
  | relabel (σ : α ≃ α) (W : SchemeCollection α) :
      ElementarySchemeMove W (W.map (LabellingScheme.relabel σ))
  | reverseLabel (a : α) (W : SchemeCollection α) :
      ElementarySchemeMove W (W.map (LabellingScheme.reverseLabel a))
  | cyclic (pre post : SchemeCollection α) (u v : LabellingScheme α) :
      ElementarySchemeMove
        (pre ++ [u ++ v] ++ post)
        (pre ++ [v ++ u] ++ post)
  | flip (pre post : SchemeCollection α) (w : LabellingScheme α) :
      ElementarySchemeMove
        (pre ++ [w] ++ post)
        (pre ++ [w.inverse] ++ post)
  | cancel (pre post : SchemeCollection α) (u v : LabellingScheme α)
      (a : α) (s : OrientationSign) :
      ElementarySchemeMove
        (pre ++ [u ++ [⟨a, s⟩, ⟨a, s.flip⟩] ++ v] ++ post)
        (pre ++ [u ++ v] ++ post)
  | uncancel (pre post : SchemeCollection α) (u v : LabellingScheme α)
      (a : α) (s : OrientationSign) :
      ElementarySchemeMove
        (pre ++ [u ++ v] ++ post)
        (pre ++ [u ++ [⟨a, s⟩, ⟨a, s.flip⟩] ++ v] ++ post)

/-- Equivalence generated by the elementary scheme operations. -/
def SchemeEquivalent {α : Type*} [DecidableEq α] :
    SchemeCollection α → SchemeCollection α → Prop :=
  Relation.EqvGen ElementarySchemeMove

/-- Polygonal edge-pasting data for a finite or infinite family of faces. -/
structure PolygonPasting (Face Label : Type*) where
  sideCount : Face → ℕ
  region : ∀ f, PolygonalRegion (sideCount f)
  direction : ∀ f, Fin (sideCount f) → EdgeDirection
  label : ∀ f, Fin (sideCount f) → Label

namespace PolygonPasting

universe u v

variable {Face : Type u} {Label : Type v} (P : PolygonPasting Face Label)

/-- Disjoint union of the filled polygonal faces before pasting. -/
abbrev PreRealization := Σ f, (P.region f).carrier

/-- A boundary point of a face, parameterized compatibly with its chosen edge orientation. -/
def sidePoint (f : Face) (i : Fin (P.sideCount f)) (t : unitInterval) : P.PreRealization :=
  ⟨f, (P.region f).edgePoint i (P.direction f i) t⟩

/-- Elementary identifications: equally labelled oriented sides are identified at equal affine
parameter. -/
inductive Generator : P.PreRealization → P.PreRealization → Prop
  | glue {f g : Face} {i : Fin (P.sideCount f)} {j : Fin (P.sideCount g)}
      (h : P.label f i = P.label g j) (t : unitInterval) :
      Generator (P.sidePoint f i t) (P.sidePoint g j t)

/-- Equivalence relation generated by the prescribed edge identifications. -/
def setoid : Setoid P.PreRealization :=
  Relation.EqvGen.setoid P.Generator

/-- Quotient obtained by pasting equally labelled oriented polygon edges. -/
abbrev Realization := Quotient P.setoid

/-- Quotient map from the disjoint union of polygonal regions. -/
def quotMk : P.PreRealization → P.Realization :=
  @Quotient.mk' _ P.setoid

/-- Signed boundary word of one face in cyclic edge order. -/
def scheme (f : Face) : LabellingScheme Label :=
  List.ofFn fun i : Fin (P.sideCount f) => ⟨P.label f i, (P.direction f i).sign⟩

end PolygonPasting

/-- Labels for the orientable genus-`n` normal form. -/
inductive OrientableSurfaceLabel (n : ℕ)
  | a : Fin n → OrientableSurfaceLabel n
  | b : Fin n → OrientableSurfaceLabel n
deriving DecidableEq, Repr

/-- One commutator block `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹`. -/
def orientableHandleBlock {n : ℕ} (i : Fin n) :
    LabellingScheme (OrientableSurfaceLabel n) :=
  [⟨.a i, .pos⟩, ⟨.b i, .pos⟩, ⟨.a i, .neg⟩, ⟨.b i, .neg⟩]

/-- The canonical labelling scheme of the `n`-fold torus. -/
def nFoldTorusScheme (n : ℕ) : LabellingScheme (OrientableSurfaceLabel n) :=
  (List.ofFn fun i : Fin n => orientableHandleBlock i).flatten

/-- Labels for the nonorientable genus-`m` normal form. -/
inductive ProjectiveSurfaceLabel (m : ℕ)
  | a : Fin m → ProjectiveSurfaceLabel m
deriving DecidableEq, Repr

/-- One crosscap block `aᵢaᵢ`. -/
def projectiveCrosscapBlock {m : ℕ} (i : Fin m) :
    LabellingScheme (ProjectiveSurfaceLabel m) :=
  [⟨.a i, .pos⟩, ⟨.a i, .pos⟩]

/-- The canonical labelling scheme of the `m`-fold projective plane. -/
def mFoldProjectivePlaneScheme (m : ℕ) : LabellingScheme (ProjectiveSurfaceLabel m) :=
  (List.ofFn fun i : Fin m => projectiveCrosscapBlock i).flatten


/-- One-face polygon pasting determined by a signed labelling scheme. -/
def schemePasting {α : Type*} (w : LabellingScheme α)
    (P : PolygonalRegion w.length) : PolygonPasting PUnit α where
  sideCount _ := w.length
  region _ := P
  direction _ i :=
    match (w.get i).sign with
    | .pos => .forward
    | .neg => .reverse
  label _ i := (w.get i).label

/-- The quotient space obtained by pasting a polygon according to a signed labelling scheme. -/
abbrev schemeRealization {α : Type*} (w : LabellingScheme α)
    (P : PolygonalRegion w.length) :=
  (schemePasting w P).Realization

/-- The `n`-fold torus as the quotient space defined by its canonical commutator scheme
(FC02-C12-U013). -/
abbrev nFoldTorus (n : ℕ) (P : PolygonalRegion (nFoldTorusScheme n).length) :=
  schemeRealization (nFoldTorusScheme n) P

/-- The `m`-fold projective plane as the quotient space defined by its canonical crosscap scheme
(FC02-C12-U015). -/
abbrev mFoldProjectivePlane (m : ℕ)
    (P : PolygonalRegion (mFoldProjectivePlaneScheme m).length) :=
  schemeRealization (mFoldProjectivePlaneScheme m) P

end LeanCategories.Topology
