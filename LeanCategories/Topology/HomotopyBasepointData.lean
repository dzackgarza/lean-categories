/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.HomotopyGroups

/-!
# Change of basepoint for higher homotopy groups

Definition-level realization of Hatcher FC07-C04-U002.

Given a path `γ : x₀ ⟶ x₁` and an `n`-loop `f` based at `x₁`,
Hatcher constructs `γf` by shrinking `f` to a concentric half-size cube and
using `γ` along radial segments in the surrounding shell.  The induced map on
homotopy classes is the change-of-basepoint map `β_γ`.

Sweep III records the inner-cube placement, the representative construction
through its exact source graph, and the induced class-map specification.  It
does not prove existence/continuity of the radial extension, descent through
homotopy, additivity, path-composition laws, or invertibility.
-/

@[expose] public noncomputable section

open scoped Topology Topology.Homotopy

namespace LeanCategories.Topology

universe u

/-- Source specification for the concentric half-size cube in Hatcher's
absolute change-of-basepoint construction. -/
def IsHomotopyBasepointInnerCubeData
    (n : ℕ)
    (e : (Fin n → unitInterval) → (Fin n → unitInterval)) : Prop :=
  ∀ t i, (e t i : ℝ) = 1 / 4 + (t i : ℝ) / 2

/-- Source-faithful concentric half-size cube data. -/
abbrev HomotopyBasepointInnerCubeData (n : ℕ) :=
  {e : (Fin n → unitInterval) → (Fin n → unitInterval) //
    IsHomotopyBasepointInnerCubeData n e}

/-- Exact source-level graph of Hatcher's representative `γf`.

On the concentric half-size cube this is `f`; in the surrounding shell its
values lie on `γ`.  The shell parameter records Hatcher's radial
reparametrization without importing the extension/continuity proof. -/
def IsHomotopyBasepointRepresentativeData
    {X : Type u} [TopologicalSpace X] {x0 x1 : X} {n : ℕ}
    (e : HomotopyBasepointInnerCubeData n)
    (γ : Path x0 x1)
    (f : GenLoop (Fin n) X x1)
    (g : GenLoop (Fin n) X x0) : Prop :=
  (∀ t, g (e.1 t) = f t) ∧
    ∃ ρ : (Fin n → unitInterval) → unitInterval,
      ∀ y, y ∉ Set.range e.1 → g y = γ (ρ y)

/-- Source-faithful representative data for Hatcher's `γf`. -/
abbrev HomotopyBasepointRepresentativeData
    {X : Type u} [TopologicalSpace X] {x0 x1 : X} {n : ℕ}
    (e : HomotopyBasepointInnerCubeData n)
    (γ : Path x0 x1)
    (f : GenLoop (Fin n) X x1) :=
  {g : GenLoop (Fin n) X x0 //
    IsHomotopyBasepointRepresentativeData e γ f g}

/-- A certified representative construction for every based `n`-loop. -/
structure HomotopyBasepointRepresentativeSystemData
    {X : Type u} [TopologicalSpace X] {x0 x1 : X}
    (γ : Path x0 x1) (n : ℕ) where
  innerCube : HomotopyBasepointInnerCubeData n
  representative : ∀ f : GenLoop (Fin n) X x1,
    HomotopyBasepointRepresentativeData innerCube γ f

/-- Exact source specification for the change-of-basepoint map on homotopy
classes.  It records only `[f] ↦ [γf]`; representative-independence is not
proved in Sweep III. -/
def IsHomotopyBasepointClassMapData
    (X : Type u) [TopologicalSpace X] (x0 x1 : X)
    (γ : Path x0 x1) (n : ℕ) (_hn : 0 < n)
    (D : HomotopyBasepointRepresentativeSystemData γ n)
    (β : HomotopyGroup.Pi n X x1 → HomotopyGroup.Pi n X x0) : Prop :=
  ∀ f : GenLoop (Fin n) X x1,
    β (Quotient.mk' f) =
      Quotient.mk' (D.representative f).1

/-- Source-faithful change-of-basepoint class-map data relative to supplied
representative data. -/
abbrev HomotopyBasepointClassMapData
    (X : Type u) [TopologicalSpace X] (x0 x1 : X)
    (γ : Path x0 x1) (n : ℕ) (hn : 0 < n)
    (D : HomotopyBasepointRepresentativeSystemData γ n) :=
  {β : HomotopyGroup.Pi n X x1 → HomotopyGroup.Pi n X x0 //
    IsHomotopyBasepointClassMapData X x0 x1 γ n hn D β}

/-- A certified change-of-basepoint construction for every path. -/
abbrev HomotopyBasepointClassMapSystemData
    (X : Type u) [TopologicalSpace X] (x0 x1 : X)
    (n : ℕ) (hn : 0 < n) :=
  ∀ γ : Path x0 x1,
    Σ D : HomotopyBasepointRepresentativeSystemData γ n,
      HomotopyBasepointClassMapData X x0 x1 γ n hn D

/-- The class in `π₁(X,x)` represented by a based loop `γ`.  Mathlib's
native equivalence with the fundamental group is used only as the quotient
carrier identification. -/
def homotopyPiOneClassData
    {X : Type u} [TopologicalSpace X] {x : X}
    (γ : Path x x) : HomotopyGroup.Pi 1 X x :=
  (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).symm
    (Path.Homotopic.Quotient.mk γ)

/-- Raw carrier of Hatcher's `π₁` action on `π_n`, before asserting that
the action maps are automorphisms or that the assignment is a homomorphism. -/
abbrev HomotopyPiOneActionData
    (X : Type u) [TopologicalSpace X] (x : X) (n : ℕ) :=
  HomotopyGroup.Pi 1 X x →
    HomotopyGroup.Pi n X x → HomotopyGroup.Pi n X x

/-- Exact source specification of the action assignment:
`[γ]` acts by the change-of-basepoint map `β_γ`. -/
def IsHomotopyPiOneActionData
    (X : Type u) [TopologicalSpace X] (x : X)
    (n : ℕ) (hn : 0 < n)
    (D : HomotopyBasepointClassMapSystemData X x x n hn)
    (act : HomotopyPiOneActionData X x n) : Prop :=
  ∀ γ : Path x x,
    act (homotopyPiOneClassData γ) =
      (D γ).2.1

/-- Source-faithful raw `π₁`-action data relative to supplied certified
change-of-basepoint maps. -/
abbrev HomotopyPiOneActionPresentationData
    (X : Type u) [TopologicalSpace X] (x : X)
    (n : ℕ) (hn : 0 < n)
    (D : HomotopyBasepointClassMapSystemData X x x n hn) :=
  {act : HomotopyPiOneActionData X x n //
    IsHomotopyPiOneActionData X x n hn D act}

end LeanCategories.Topology
