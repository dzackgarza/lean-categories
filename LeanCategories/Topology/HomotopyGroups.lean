/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SmashProduct
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Maps and elementary predicates for homotopy groups

Mathlib supplies the homotopy groups themselves, but the project needs a reusable induced-map
interface in order to state source definitions such as weak homotopy equivalence.  This file owns
that generic topology-level construction; stable-spectrum code reuses it rather than defining a
second copy in homological algebra.
-/

@[expose] public section

noncomputable section

open scoped Topology Topology.Homotopy

namespace LeanCategories.Topology

universe u v

/-- Postcomposition by a continuous map sends a generalized loop based at `x` to one based at
`f x`. -/
def genLoopMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (N : Type*) (p : GenLoop N X x) : GenLoop N Y (f x) :=
  ⟨f.comp p.1, by
    intro z hz
    exact congrArg f (p.2 z hz)⟩

/-- Postcomposition preserves homotopy relative to the boundary of the cube. -/
theorem genLoopMap_homotopic {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {N : Type*} {p q : GenLoop N X x}
    (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopMap f x N p) (genLoopMap f x N q) := by
  change (f.comp p.1).HomotopicRel (f.comp q.1) (Cube.boundary N)
  exact h.comp_continuousMap f

/-- The map on homotopy groups induced by a continuous map, at a chosen source basepoint.

For `N = Fin n` this is the usual map `π_n(X,x) → π_n(Y,f x)`.
-/
def homotopyGroupMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (N : Type*) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (genLoopMap f x N) (fun _ _ h => genLoopMap_homotopic f h)

/-- Postcomposition by a based map sends generalized loops at the distinguished point to
generalized loops at the distinguished point. -/
def basedGenLoopMap {X Y : BasedTop.{u}} (f : X ⟶ Y) (N : Type*)
    (p : GenLoop N X.right X.point) : GenLoop N Y.right Y.point :=
  ⟨f.right.hom.comp p.1, by
    intro z hz
    change f.right (p z) = Y.point
    calc
      f.right (p z) = f.right X.point := congrArg f.right (p.2 z hz)
      _ = Y.point := BasedTop.map_point f⟩

/-- Postcomposition by a based map preserves boundary-relative homotopy. -/
theorem basedGenLoopMap_homotopic {X Y : BasedTop.{u}} (f : X ⟶ Y) {N : Type*}
    {p q : GenLoop N X.right X.point} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (basedGenLoopMap f N p) (basedGenLoopMap f N q) := by
  change (f.right.hom.comp p.1).HomotopicRel (f.right.hom.comp q.1) (Cube.boundary N)
  exact h.comp_continuousMap f.right.hom

/-- The homotopy-group map induced by a based continuous map. -/
def basedHomotopyGroupMap {X Y : BasedTop.{u}} (f : X ⟶ Y) (N : Type*) :
    HomotopyGroup N X.right X.point → HomotopyGroup N Y.right Y.point :=
  Quotient.map (basedGenLoopMap f N) (fun _ _ h => basedGenLoopMap_homotopic f h)

/-- A based space is `n`-connected when it is path connected and its positive-degree homotopy
groups through degree `n` are trivial.

Source: Hatcher, *Algebraic Topology*, §4.1, Definition at p. 346 (FC07-C04-U012). -/
def IsNConnected (X : BasedTop.{u}) (n : ℕ) : Prop :=
  PathConnectedSpace X.right ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ n → Subsingleton (HomotopyGroup.Pi i X.right X.point)

/-- A continuous map is a weak homotopy equivalence when it induces bijections on every homotopy
group at every choice of source basepoint, including degree zero.

For positive degrees the induced maps are the standard postcomposition maps on homotopy groups;
degree zero is Mathlib's `π₀`, equivalent to `ZerothHomotopy`.

Source: Hatcher, *Algebraic Topology*, §4.1, p. 346 (FC07-C04-U022). -/
def IsWeakHomotopyEquivalence {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : Prop :=
  ∀ (x : X) (n : ℕ), Function.Bijective (homotopyGroupMap f x (Fin n))

/-- Data exhibiting a based space as an Eilenberg--Mac Lane space `K(G,n)`.

The distinguished homotopy group is identified with `G` as a group, not merely as a type.  The
standard consequence that `G` is abelian when `n ≥ 2` follows from Mathlib's commutative-group
instance on higher homotopy groups and is theorem content rather than an extra definitional
field.

Source: Hatcher, *Algebraic Topology*, §4.2, p. 360 (FC07-C04-U042). -/
structure EilenbergMacLaneStructure (X : BasedTop.{u}) (G : Type v) [Group G] (n : ℕ) where
  n_pos : 0 < n
  pathConnected : PathConnectedSpace X.right
  groupEquiv :
    (letI : Nonempty (Fin n) := ⟨⟨0, n_pos⟩⟩;
      HomotopyGroup.Pi n X.right X.point ≃* G)
  otherTrivial :
    ∀ i : ℕ, i ≠ n → Subsingleton (HomotopyGroup.Pi i X.right X.point)

/-- Predicate that a based space is an Eilenberg--Mac Lane space `K(G,n)`.

Source: Hatcher, *Algebraic Topology*, §4.2, p. 360 (FC07-C04-U042). -/
def IsEilenbergMacLane (X : BasedTop.{u}) (G : Type v) [Group G] (n : ℕ) : Prop :=
  Nonempty (EilenbergMacLaneStructure X G n)

end LeanCategories.Topology
