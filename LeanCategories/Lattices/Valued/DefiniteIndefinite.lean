/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Signature

/-!
# Definite, indefinite, and root loci of the lattice category

There is one category of finite projective integral lattices,
`FiniteProjectiveLatticeCat ℤ ℤ`. Definiteness, indefiniteness, and the root condition are
properties of its objects, so the theories built on them are full subcategories of that one
category, not competing definitions of a lattice.

Each locus carries its own theory:

* definite lattices: minima, short vectors, representation numbers, theta series, class
  numbers, and mass formulas;
* indefinite lattices: isotropic vectors, hyperbolic planes, the Witt index, and strong
  approximation;
* root lattices: a definite locus, where the reflections in the roots generate a Weyl group.

Every predicate here is stated through the real signature `integralSignature`, so a lattice
property is a property of its Sylvester invariants and is therefore an isometry invariant.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

/-- The definite locus. A lattice is definite when it is positive definite or negative
definite; both cases carry the nondegeneracy demanded by `IsPositiveDefiniteSignature` and
`IsNegativeDefiniteSignature`, so a definite lattice has zero null part. The convention keeps
both signs, because negation of the form exchanges them and is an equivalence of the theory. -/
def isDefiniteLattice : ObjectProperty (FiniteProjectiveLatticeCat ℤ ℤ) :=
  fun L ↦ IsPositiveDefiniteLattice L ∨ IsNegativeDefiniteLattice L

/-- The category of definite finite integral lattices. -/
abbrev DefiniteLatticeCat := isDefiniteLattice.FullSubcategory

/-- Forget definiteness. -/
def definiteForget : DefiniteLatticeCat ⥤ FiniteProjectiveLatticeCat ℤ ℤ :=
  isDefiniteLattice.ι

/-- The indefinite locus: both signed ranks of the real signature are nonzero. -/
def isIndefiniteLattice : ObjectProperty (FiniteProjectiveLatticeCat ℤ ℤ) :=
  fun L ↦ IsIndefiniteLattice L

/-- The category of indefinite finite integral lattices. -/
abbrev IndefiniteLatticeCat := isIndefiniteLattice.FullSubcategory

/-- Forget indefiniteness. -/
def indefiniteForget : IndefiniteLatticeCat ⥤ FiniteProjectiveLatticeCat ℤ ℤ :=
  isIndefiniteLattice.ι

/-- A lattice with zero null part is definite or indefinite. -/
theorem isDefiniteLattice_or_isIndefiniteLattice
    (L : FiniteProjectiveLatticeCat ℤ ℤ) (h : (integralSignature L).2.2 = 0) :
    isDefiniteLattice L ∨ isIndefiniteLattice L := by
  change (IsPositiveDefiniteSignature (integralSignature L) ∨
      IsNegativeDefiniteSignature (integralSignature L)) ∨
    IsIndefiniteSignature (integralSignature L)
  generalize integralSignature L = s at h ⊢
  obtain ⟨p, n, z⟩ := s
  simp only [IsPositiveDefiniteSignature, IsNegativeDefiniteSignature,
    IsIndefiniteSignature] at h ⊢
  omega

/-- The definite locus and the indefinite locus are disjoint. -/
theorem not_isIndefiniteLattice_of_isDefiniteLattice
    {L : FiniteProjectiveLatticeCat ℤ ℤ} (h : isDefiniteLattice L) :
    ¬ isIndefiniteLattice L := by
  revert h
  change (IsPositiveDefiniteSignature (integralSignature L) ∨
      IsNegativeDefiniteSignature (integralSignature L)) →
    ¬ IsIndefiniteSignature (integralSignature L)
  generalize integralSignature L = s
  obtain ⟨p, n, z⟩ := s
  simp only [IsPositiveDefiniteSignature, IsNegativeDefiniteSignature,
    IsIndefiniteSignature]
  omega

/-- The root locus, on the definite lattices only: the roots of `IsRoot`, the vectors of
self-pairing `±1` or `±2`, span the carrier. The predicate lives here rather than in
`RootSystem.lean` because that file supplies the reflective vectors and their Weyl group for an
arbitrary lattice, while the spanning condition is only used as a locus of the definite
category. -/
def isRootLattice : ObjectProperty DefiniteLatticeCat :=
  fun L ↦ Submodule.span ℤ {x : L.obj.obj.obj.carrier | IsRoot L.obj.obj x} = ⊤

/-- The category of definite root lattices. -/
abbrev RootLatticeCat := isRootLattice.FullSubcategory

/-- Forget the root condition. -/
def rootForget : RootLatticeCat ⥤ DefiniteLatticeCat :=
  isRootLattice.ι

end LeanCategories.Lattices.Valued
