/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Fiber-preserving maps and fiber homotopy equivalences

This file packages the standard over-a-fixed-base notions from Hatcher, Chapter 4.  The carrier
maps and homotopies are Mathlib continuous maps and `ContinuousMap.HomotopyWith`; the project adds
only the equations saying that they remain over the chosen base.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

universe u v w

variable {B : Type u} [TopologicalSpace B]
variable {E₁ : Type v} [TopologicalSpace E₁]
variable {E₂ : Type w} [TopologicalSpace E₂]

/-- A continuous map between total spaces over a common base is fiber-preserving when it commutes
with the two projections.

Source: Hatcher, *Algebraic Topology*, §4.3, p. 380 (FC07-C04-U085). -/
@[ext]
structure FiberPreservingMap (p₁ : C(E₁, B)) (p₂ : C(E₂, B)) where
  toContinuousMap : C(E₁, E₂)
  comm : p₂.comp toContinuousMap = p₁

namespace FiberPreservingMap

/-- Identity as a fiber-preserving map. -/
def id (p : C(E₁, B)) : FiberPreservingMap p p where
  toContinuousMap := ContinuousMap.id E₁
  comm := by ext; rfl

/-- Composition of fiber-preserving maps. -/
def comp {E₃ : Type*} [TopologicalSpace E₃] {p₁ : C(E₁, B)} {p₂ : C(E₂, B)}
    {p₃ : C(E₃, B)} (f : FiberPreservingMap p₁ p₂) (g : FiberPreservingMap p₂ p₃) :
    FiberPreservingMap p₁ p₃ where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  comm := by rw [← ContinuousMap.comp_assoc, g.comm, f.comm]

end FiberPreservingMap

/-- A homotopy through fiber-preserving maps.  At every time, the intermediate continuous map
commutes with the projection to the common base.

Source: Hatcher, *Algebraic Topology*, §4.3, p. 380 (FC07-C04-U085). -/
abbrev FiberPreservingHomotopy {p₁ : C(E₁, B)} {p₂ : C(E₂, B)}
    (f g : FiberPreservingMap p₁ p₂) :=
  ContinuousMap.HomotopyWith f.toContinuousMap g.toContinuousMap
    (fun h => p₂.comp h = p₁)

/-- A fiber homotopy equivalence is a fiber-preserving map with a fiber-preserving inverse up to
homotopy through fiber-preserving maps.

Source: Hatcher, *Algebraic Topology*, §4.3, p. 380 (FC07-C04-U085). -/
structure FiberHomotopyEquivalence (p₁ : C(E₁, B)) (p₂ : C(E₂, B)) where
  hom : FiberPreservingMap p₁ p₂
  inv : FiberPreservingMap p₂ p₁
  hom_inv : FiberPreservingHomotopy (FiberPreservingMap.comp hom inv) (FiberPreservingMap.id p₁)
  inv_hom : FiberPreservingHomotopy (FiberPreservingMap.comp inv hom) (FiberPreservingMap.id p₂)

end LeanCategories.Topology
