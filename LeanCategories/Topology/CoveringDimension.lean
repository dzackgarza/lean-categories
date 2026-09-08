/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Covering dimension in the sense of Munkres

This file realizes FC02-C08-U012--U014 from Munkres, *Topology*.

The Sweep-II reference `google-deepmind/formal-conjectures` commit
`8323e878b83fcd7f4a448256069352a265460d75`, file
`FormalConjecturesForMathlib/Topology/LebesgueCoveringDimension.lean`, is
Apache-2.0 and defines the analogous notion for **finite** open covers.  Munkres'
source unit quantifies over arbitrary open covers, so the definitions below keep
the stronger source quantifier instead of silently importing the finite-cover
variant.
-/

namespace LeanCategories.Topology

open Set

universe u

/-- A family `𝓥` refines `𝓤` when every member of `𝓥` is contained in a member
of `𝓤` (FC02-C08-U013). -/
def Refines {X : Type u} (𝓥 𝓤 : Set (Set X)) : Prop :=
  ∀ V ∈ 𝓥, ∃ U ∈ 𝓤, V ⊆ U

/-- A collection has order at most `n` when no point belongs to more than `n`
members.  This is the order bound underlying FC02-C08-U012. -/
def CoverOrderLE {X : Type u} (𝓤 : Set (Set X)) (n : ℕ) : Prop :=
  ∀ x : X, {U ∈ 𝓤 | x ∈ U}.encard ≤ (n : ℕ)

/-- A family is an open cover of the whole space. -/
def IsOpenCoverFamily {X : Type u} [TopologicalSpace X] (𝓤 : Set (Set X)) : Prop :=
  (∀ U ∈ 𝓤, IsOpen U) ∧ ⋃₀ 𝓤 = Set.univ

/-- Munkres covering dimension at most `n`: every open cover admits an open
refinement of order at most `n + 1` (FC02-C08-U014). -/
def HasMunkresCoveringDimensionLE (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ 𝓤 : Set (Set X), IsOpenCoverFamily 𝓤 →
    ∃ 𝓥 : Set (Set X), IsOpenCoverFamily 𝓥 ∧ Refines 𝓥 𝓤 ∧ CoverOrderLE 𝓥 (n + 1)

/-- A space is finite-dimensional in Munkres' sense when some natural number
bounds its covering dimension (FC02-C08-U014). -/
def IsMunkresFiniteDimensional (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, HasMunkresCoveringDimensionLE X n

/-- The assertion that Munkres covering dimension is exactly `n`.  This avoids
choosing a default value for spaces that are not finite-dimensional. -/
def HasMunkresCoveringDimensionEq (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  HasMunkresCoveringDimensionLE X n ∧
    ∀ m : ℕ, m < n → ¬ HasMunkresCoveringDimensionLE X m

end LeanCategories.Topology
