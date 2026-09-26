/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Profinite local reciprocity data

Definition-level realization of Serre FC10-C13-U031.

For an infinite Galois extension, Serre defines the Artin symbol by requiring
all of its finite Galois projections to be the already-defined finite Artin
symbols. Proposition 12 supplies the compatibility of those finite symbols.

Sweep III records exactly this projection graph as data. It does not prove
finite-stage compatibility, existence/uniqueness of a function satisfying the
graph, or the subsequent
identification of the maximal abelian Galois group with the Hausdorff
completion in the norm topology.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w

/-- Projection graph characterizing Serre's Artin map for an infinite abelian
Galois extension.

`finiteArtin i x` is the finite Artin symbol at stage `i`, while
`projection i` is restriction from the infinite abelian Galois group to that
finite quotient. -/
def IsProfiniteLocalArtinMapData
    {Index : Type u} {KStar : Type v}
    {FiniteGalois : Index → Type w} {G : Type w}
    [∀ i, CommGroup (FiniteGalois i)] [CommGroup G]
    (projection : ∀ i, G → FiniteGalois i)
    (finiteArtin : ∀ i, KStar → FiniteGalois i)
    (artin : KStar → G) : Prop :=
  ∀ x i, projection i (artin x) = finiteArtin i x

/-- Source-faithful infinite Artin-map data: a function together with the
exact graph of all finite Galois projections. FC10-C13-U030 supplies
existence/uniqueness from finite-stage compatibility. -/
abbrev ProfiniteLocalArtinMapData
    {Index : Type u} {KStar : Type v}
    {FiniteGalois : Index → Type w} {G : Type w}
    [∀ i, CommGroup (FiniteGalois i)] [CommGroup G]
    (projection : ∀ i, G → FiniteGalois i)
    (finiteArtin : ∀ i, KStar → FiniteGalois i) :=
  {artin : KStar → G //
    IsProfiniteLocalArtinMapData projection finiteArtin artin}

/-- Serre's symbol `(x,F/E)` for the supplied infinite abelian Galois
extension presentation. -/
def profiniteLocalArtinSymbolData
    {Index : Type u} {KStar : Type v}
    {FiniteGalois : Index → Type w} {G : Type w}
    [∀ i, CommGroup (FiniteGalois i)] [CommGroup G]
    (projection : ∀ i, G → FiniteGalois i)
    (finiteArtin : ∀ i, KStar → FiniteGalois i)
    (D : ProfiniteLocalArtinMapData projection finiteArtin)
    (x : KStar) : G :=
  D.1 x

end LeanCategories.Algebra
