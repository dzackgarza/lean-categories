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

Sweep III records exactly this projection graph and selects the resulting
infinite symbol as data. It does not prove the finite-stage compatibility, the
existence/uniqueness statement for the selected function, or the subsequent
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

/-- Serre's Artin map for an infinite abelian extension, selected from its
finite-projection graph.

The theorem layer uses finite-symbol compatibility (FC10-C13-U030) to prove
that this selected map satisfies `IsProfiniteLocalArtinMapData`. -/
def profiniteLocalArtinMapData
    {Index : Type u} {KStar : Type v}
    {FiniteGalois : Index → Type w} {G : Type w}
    [∀ i, CommGroup (FiniteGalois i)] [CommGroup G]
    (projection : ∀ i, G → FiniteGalois i)
    (finiteArtin : ∀ i, KStar → FiniteGalois i) :
    KStar → G := by
  letI : Nonempty (KStar → G) := ⟨fun _ => 1⟩
  exact Classical.epsilon
    (IsProfiniteLocalArtinMapData projection finiteArtin)

/-- Serre's symbol `(x,F/E)` for the supplied infinite abelian Galois
extension presentation. -/
def profiniteLocalArtinSymbolData
    {Index : Type u} {KStar : Type v}
    {FiniteGalois : Index → Type w} {G : Type w}
    [∀ i, CommGroup (FiniteGalois i)] [CommGroup G]
    (projection : ∀ i, G → FiniteGalois i)
    (finiteArtin : ∀ i, KStar → FiniteGalois i)
    (x : KStar) : G :=
  profiniteLocalArtinMapData projection finiteArtin x

end LeanCategories.Algebra
