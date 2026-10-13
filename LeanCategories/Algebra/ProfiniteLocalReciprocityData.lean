/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Basic

/-!
# Profinite local reciprocity data

Definition-level realization of Serre FC10-C13-U031.

For an infinite abelian Galois extension, Serre defines the Artin symbol by
its compatible finite Galois projections.  FC10-C13-U030 supplies exactly
that compatibility.  This file therefore represents the infinite group by
the genuine compatible-tuple inverse-limit carrier and constructs the Artin
symbol componentwise.  No fallback element or selected candidate occurs.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w

/-- Finite-stage data for Serre's inverse system of abelian Galois groups.
The compatibility field is the preceding finite-Artin compatibility result
needed to place the finite symbols in the inverse-limit carrier. -/
structure ProfiniteLocalGaloisSystemData
    (Index : Type u) [Preorder Index]
    (KStar : Type v) (FiniteGalois : Index → Type w)
    [∀ i, CommGroup (FiniteGalois i)] where
  transition : ∀ {i j : Index}, i ≤ j → FiniteGalois j → FiniteGalois i
  finiteArtin : ∀ i, KStar → FiniteGalois i
  finiteArtin_compatible :
    ∀ {i j : Index} (hij : i ≤ j) (x : KStar),
      transition hij (finiteArtin j x) = finiteArtin i x

/-- The inverse-limit carrier: compatible tuples of finite-stage Galois
elements. -/
abbrev ProfiniteLocalGaloisLimitData
    {Index : Type u} [Preorder Index]
    {KStar : Type v} {FiniteGalois : Index → Type w}
    [∀ i, CommGroup (FiniteGalois i)]
    (S : ProfiniteLocalGaloisSystemData Index KStar FiniteGalois) : Type _ :=
  {g : ∀ i, FiniteGalois i //
    ∀ {i j : Index} (hij : i ≤ j), S.transition hij (g j) = g i}

/-- Native projection from the compatible-tuple inverse limit to a finite
stage. -/
def profiniteLocalProjectionData
    {Index : Type u} [Preorder Index]
    {KStar : Type v} {FiniteGalois : Index → Type w}
    [∀ i, CommGroup (FiniteGalois i)]
    (S : ProfiniteLocalGaloisSystemData Index KStar FiniteGalois)
    (i : Index) : ProfiniteLocalGaloisLimitData S → FiniteGalois i :=
  fun g => g.1 i

/-- Projection graph characterizing Serre's infinite Artin map. -/
def IsProfiniteLocalArtinMapData
    {Index : Type u} [Preorder Index]
    {KStar : Type v} {FiniteGalois : Index → Type w}
    [∀ i, CommGroup (FiniteGalois i)]
    (S : ProfiniteLocalGaloisSystemData Index KStar FiniteGalois)
    (artin : KStar → ProfiniteLocalGaloisLimitData S) : Prop :=
  ∀ x i, profiniteLocalProjectionData S i (artin x) = S.finiteArtin i x

/-- Serre's infinite Artin map, constructed componentwise as the compatible
tuple of its finite Artin symbols. -/
def profiniteLocalArtinMapData
    {Index : Type u} [Preorder Index]
    {KStar : Type v} {FiniteGalois : Index → Type w}
    [∀ i, CommGroup (FiniteGalois i)]
    (S : ProfiniteLocalGaloisSystemData Index KStar FiniteGalois) :
    KStar → ProfiniteLocalGaloisLimitData S :=
  fun x => ⟨fun i => S.finiteArtin i x, fun hij => S.finiteArtin_compatible hij x⟩

/-- Serre's symbol `(x,F/E)` in the compatible-tuple inverse-limit model. -/
def profiniteLocalArtinSymbolData
    {Index : Type u} [Preorder Index]
    {KStar : Type v} {FiniteGalois : Index → Type w}
    [∀ i, CommGroup (FiniteGalois i)]
    (S : ProfiniteLocalGaloisSystemData Index KStar FiniteGalois)
    (x : KStar) : ProfiniteLocalGaloisLimitData S :=
  profiniteLocalArtinMapData S x

end LeanCategories.Algebra
