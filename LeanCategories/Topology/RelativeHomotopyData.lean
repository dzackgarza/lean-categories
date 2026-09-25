/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.HomotopyGroups

/-!
# Relative homotopy data

Definition-level realization of Hatcher FC07-C04-U007.

For a based pair `x₀ ∈ A ⊆ X` and `n > 0`, a relative `n`-cube sends the
whole boundary of `I^n` into `A` and sends `J^{n-1}` to `x₀`, where
`J^{n-1}` is the union of all faces except the distinguished last-coordinate
zero face. Relative homotopies preserve the same two conditions.

Sweep III records the relative maps, their homotopy-class quotient, the
source concatenation formula, and a candidate group constrained by that
formula for `n ≥ 2`. It does not prove that relative homotopy is an
equivalence relation, that concatenation descends through the quotient, the
group laws, or commutativity for `n ≥ 3`; those are result-layer obligations.
-/

@[expose] public noncomputable section

open scoped Topology Topology.Homotopy

namespace LeanCategories.Topology

universe u

/-- The distinguished last coordinate in Hatcher's positive-dimensional
relative cube. -/
def relativeHomotopyLastCoordinate (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

/-- Hatcher's `J^{n-1}`: every cubical face except the distinguished
last-coordinate zero face. -/
def relativeHomotopyJData (n : ℕ) (hn : 0 < n) :
    Set (Fin n → unitInterval) :=
  {y |
    y (relativeHomotopyLastCoordinate n hn) = 1 ∨
      ∃ i : Fin n,
        i ≠ relativeHomotopyLastCoordinate n hn ∧
          (y i = 0 ∨ y i = 1)}

/-- A relative `n`-cube for `(X,A,x₀)`: its boundary lies in `A`, and
all of `J^{n-1}` is sent to the basepoint. -/
structure RelativeGenLoopData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (n : ℕ) (hn : 0 < n) where
  toContinuousMap : C(Fin n → unitInterval, X)
  boundary_mem :
    ∀ y ∈ Cube.boundary (Fin n), toContinuousMap y ∈ A
  fixed_boundary :
    ∀ y ∈ relativeHomotopyJData n hn, toContinuousMap y = x0

/-- The constant relative cube at the distinguished point. -/
def relativeGenLoopConstData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) :
    RelativeGenLoopData X A x0 n hn where
  toContinuousMap := ContinuousMap.const _ x0
  boundary_mem := by
    intro _ _
    exact hx0
  fixed_boundary := by
    intro _ _
    rfl

namespace RelativeGenLoopData

/-- Homotopy of relative cubes: throughout the homotopy the cubical boundary
stays in `A` and `J^{n-1}` stays at `x₀`. -/
def Homotopic
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    {n : ℕ} {hn : 0 < n}
    (f g : RelativeGenLoopData X A x0 n hn) : Prop :=
  ∃ H : C(unitInterval × (Fin n → unitInterval), X),
    (∀ y, H (0, y) = f.toContinuousMap y) ∧
      (∀ y, H (1, y) = g.toContinuousMap y) ∧
        (∀ t y, y ∈ Cube.boundary (Fin n) → H (t, y) ∈ A) ∧
          ∀ t y, y ∈ relativeHomotopyJData n hn → H (t, y) = x0

end RelativeGenLoopData

/-- The raw homotopy-class carrier of relative `n`-cubes.

The later result that `RelativeGenLoopData.Homotopic` is an equivalence
relation identifies this quotient with the usual set of relative homotopy
classes. -/
abbrev RelativeHomotopyClassData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (n : ℕ) (hn : 0 < n) :=
  Quot (fun f g : RelativeGenLoopData X A x0 n hn =>
    RelativeGenLoopData.Homotopic f g)

/-- The relative homotopy class of a representative. -/
def relativeHomotopyClassMkData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    {n : ℕ} {hn : 0 < n}
    (f : RelativeGenLoopData X A x0 n hn) :
    RelativeHomotopyClassData X A x0 n hn :=
  Quot.mk _ f

/-- The distinguished class represented by the constant relative cube. -/
def relativeHomotopyBaseClassData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) :
    RelativeHomotopyClassData X A x0 n hn :=
  relativeHomotopyClassMkData
    (relativeGenLoopConstData X A x0 hx0 n hn)

/-- Exact pointwise graph of concatenation of two relative cubes in coordinate
`i`, using the same cubical subdivision as Mathlib's absolute
`GenLoop.transAt`. -/
def IsRelativeGenLoopConcatData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    {n : ℕ} {hn : 0 < n}
    (i : Fin n)
    (f g h : RelativeGenLoopData X A x0 n hn) : Prop :=
  ∀ t,
    h.toContinuousMap t =
      if (t i : ℝ) ≤ 1 / 2 then
        f.toContinuousMap
          (Function.update t i
            (Set.projIcc 0 1 zero_le_one (2 * t i)))
      else
        g.toContinuousMap
          (Function.update t i
            (Set.projIcc 0 1 zero_le_one (2 * t i - 1)))

/-- A source-formula candidate for concatenation. Its existence with the
displayed graph is a result obligation, so Sweep III selects a relative cube
without proving that graph. -/
def relativeGenLoopConcatData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    (hx0 : x0 ∈ A) {n : ℕ} {hn : 0 < n}
    (i : Fin n)
    (f g : RelativeGenLoopData X A x0 n hn) :
    RelativeGenLoopData X A x0 n hn :=
  letI : Nonempty (RelativeGenLoopData X A x0 n hn) :=
    ⟨relativeGenLoopConstData X A x0 hx0 n hn⟩
  Classical.epsilon (IsRelativeGenLoopConcatData i f g)

/-- Hatcher's canonical concatenation coordinate for `n ≥ 2`: the first
coordinate, which is distinct from the distinguished last coordinate. -/
def relativeHomotopyConcatCoordinate (n : ℕ) (h2 : 2 ≤ n) : Fin n :=
  ⟨0, by omega⟩

/-- A candidate realization of the relative homotopy group. The carrier is
equipped with group structure, while `classOf` records how the raw relative
homotopy quotient is to be identified with it. -/
structure RelativeHomotopyGroupCandidateData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (n : ℕ) (hn : 0 < n) where
  carrier : Type u
  [instGroup : Group carrier]
  classOf : RelativeHomotopyClassData X A x0 n hn → carrier

attribute [instance] RelativeHomotopyGroupCandidateData.instGroup

instance
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (RelativeHomotopyGroupCandidateData X A x0 n hn) :=
  ⟨⟨PUnit.{u + 1}, fun _ => 1⟩⟩

/-- Exact source specification for the group structure on relative homotopy
classes in degree `n ≥ 2`.

The specification asks for a bijective identification with the raw quotient,
takes the constant class to the identity, and identifies multiplication with
concatenation in the first non-distinguished coordinate. No existence,
well-definedness, or group-law proof is supplied here. -/
def IsRelativeHomotopyGroupData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    (P : RelativeHomotopyGroupCandidateData X A x0 n hn) : Prop :=
  Function.Bijective P.classOf ∧
    P.classOf (relativeHomotopyBaseClassData X A x0 hx0 n hn) = 1 ∧
      ∀ f g : RelativeGenLoopData X A x0 n hn,
        P.classOf
            (relativeHomotopyClassMkData
              (relativeGenLoopConcatData hx0
                (relativeHomotopyConcatCoordinate n h2) f g)) =
          P.classOf (relativeHomotopyClassMkData f) *
            P.classOf (relativeHomotopyClassMkData g)

/-- Hatcher's relative homotopy group candidate in degree `n ≥ 2`, selected
from its exact quotient-and-concatenation specification. -/
def relativeHomotopyGroupCandidateData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) :
    RelativeHomotopyGroupCandidateData X A x0 n hn :=
  Classical.epsilon (IsRelativeHomotopyGroupData X A x0 hx0 n hn h2)

/-- Source-facing carrier `π_n(X,A,x₀)` for `n ≥ 2`.

Its selected group structure is characterized by
`IsRelativeHomotopyGroupData`; proving that characterization is Sweep-IV
work. -/
abbrev RelativeHomotopyGroupData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) : Type u :=
  (relativeHomotopyGroupCandidateData X A x0 hx0 n hn h2).carrier

/-- Hatcher's degree-one relative homotopy object, which is only a pointed
set. -/
abbrev RelativeHomotopyPointedSetData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X) :=
  RelativeHomotopyClassData X A x0 1 (Nat.zero_lt_succ 0)

/-- Basepoint of Hatcher's degree-one relative homotopy pointed set. -/
def relativeHomotopyPointedBaseData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) :
    RelativeHomotopyPointedSetData X A x0 :=
  relativeHomotopyBaseClassData X A x0 hx0 1 (Nat.zero_lt_succ 0)

end LeanCategories.Topology
