/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Signature
public import LeanCategories.Lattices.Valued.Standard
public import Mathlib.Data.ZMod.Basic

/-!
# Boundary index modulo sixteen: definition data

Definition-level realization of Peters--Sterk FC11-C04-U046.

For a suitable oriented three-manifold `X`, Peters--Sterk choose a bounding
fourfold `Y` as in Lemma 4.4.3 and define the index of `X` modulo sixteen to be
the signed index of the intersection form `S_Y`, reduced modulo sixteen.

The target library does not currently own the required four-manifold boundary
and Rohlin interfaces.  The geometric relation saying that a lattice is the
intersection form of a suitable bounder is therefore supplied as a predicate.
Sweep III records the chosen representative and the index formula only.
Existence of a suitable bounder and independence of that choice are result
content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open LeanCategories.Lattices.Valued

/-- Missing geometric interface for FC11-C04-U046: which integral lattices
occur as the intersection forms of the bounding fourfolds for `X` admitted by
Lemma 4.4.3.

The predicate contains only the boundary/bounder relation.  Evenness of the
chosen intersection form is kept explicit in `BoundaryIndexRepresentativeData`.
-/
structure BoundingFourfoldIntersectionFormInterface
    (X : Type) [TopologicalSpace X] where
  IsSuitableBoundingIntersectionForm :
    FiniteProjectiveLatticeCat ℤ ℤ → Prop

/-- A chosen even intersection form of a suitable bounding fourfold for `X`.

No instance of this structure is produced in Sweep III; Lemma 4.4.3 is the
separate existence statement. -/
structure BoundaryIndexRepresentativeData
    (X : Type) [TopologicalSpace X]
    (B : BoundingFourfoldIntersectionFormInterface X) where
  intersectionLattice : FiniteProjectiveLatticeCat ℤ ℤ
  isSuitableBounder :
    B.IsSuitableBoundingIntersectionForm intersectionLattice
  isEven : IsEven intersectionLattice.obj

/-- Peters--Sterk's representative formula
`τ(S_Y) mod 16 = (r₊ - r₋) mod 16` for a chosen suitable bounder `Y`.

Rohlin's theorem is needed only to show that different representatives give
the same value; that proposition is not part of this definition. -/
def boundaryIndexModSixteenRepresentative
    {X : Type} [TopologicalSpace X]
    (B : BoundingFourfoldIntersectionFormInterface X)
    (d : BoundaryIndexRepresentativeData X B) : ZMod 16 :=
  (((integralSignature d.intersectionLattice).1 : ℤ) : ZMod 16) -
    (((integralSignature d.intersectionLattice).2.1 : ℤ) : ZMod 16)

/-- Peters--Sterk's index modulo sixteen `τ₁₆(X)`, computed from supplied
valid bounding-intersection-form data.

Lemma 4.4.3 supplies such data, and Rohlin's theorem proves independence of
the supplied choice; neither result is hidden in this definition. -/
def boundaryIndexModSixteen
    {X : Type} [TopologicalSpace X]
    (B : BoundingFourfoldIntersectionFormInterface X)
    (D : BoundaryIndexRepresentativeData X B) : ZMod 16 :=
  boundaryIndexModSixteenRepresentative B D

end LeanCategories.Topology
