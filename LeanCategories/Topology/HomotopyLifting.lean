/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopy lifting and extension properties

The homotopy lifting property and its arrow-dual homotopy extension property are generic
topological predicates.  They are the common owner for Hatcher's Hurewicz fibrations and
cofibrations; the project's Serre fibration specializes the lifting property to finite
polyhedra.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open scoped unitInterval

universe u v w

/-- A map `p : E → B` has the homotopy lifting property with respect to `X` when every homotopy
in `B` whose time-zero map has a prescribed lift to `E` admits a lift with that same time-zero
map. -/
def HasHomotopyLiftingProperty {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (X : Type w) [TopologicalSpace X] : Prop :=
  ∀ (g : C(X, E)) (H : C(X × unitInterval, B)),
    (∀ x, H (x, 0) = p (g x)) →
      ∃ G : C(X × unitInterval, E),
        (∀ x, G (x, 0) = g x) ∧ ∀ xt, p (G xt) = H xt

/-- A Hurewicz fibration is a continuous map having the homotopy lifting property with respect to
every topological space.

Source: Hatcher, *Algebraic Topology*, §4.3, p. 376 (FC07-C04-U083). -/
def IsHurewiczFibration {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) : Prop :=
  ∀ (X : Type w) [TopologicalSpace X], HasHomotopyLiftingProperty p X

/-- A map `i : A → B` has the homotopy extension property with respect to `Y` when a homotopy on
`A`, starting at the restriction of a map `B → Y`, extends over all of `B` while preserving the
given time-zero map. -/
def HasHomotopyExtensionProperty {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (i : C(A, B))
    (Y : Type w) [TopologicalSpace Y] : Prop :=
  ∀ (f : C(B, Y)) (H : C(A × unitInterval, Y)),
    (∀ a, H (a, 0) = f (i a)) →
      ∃ G : C(B × unitInterval, Y),
        (∀ b, G (b, 0) = f b) ∧ ∀ (a : A) (t : unitInterval), G (i a, t) = H (a, t)

/-- A Hurewicz cofibration is a continuous map having the homotopy extension property with respect
to every target space.  This is the topological arrow-dual of a Hurewicz fibration, not a
model-category cofibration.

Source: Hatcher, *Algebraic Topology*, §4.H, p. 430 (FC07-C04-U148). -/
def IsHurewiczCofibration {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (i : C(A, B)) : Prop :=
  ∀ (Y : Type w) [TopologicalSpace Y], HasHomotopyExtensionProperty i Y

end LeanCategories.Topology
