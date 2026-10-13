/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AffineAlgebraicGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Isogeny data

Definition-level reference port for Humphreys FC16-C11-U019.

For affine algebraic groups over a field, the standard group-scheme
formulation of an isogeny is a finite, flat, surjective morphism.  The
pinned TauCeti reference proves that this is the scheme-theoretic form of
Humphreys' surjective morphism with finite kernel.  Sweep III records only
the predicate, not that equivalence theorem.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

open CategoryTheory
open _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A morphism of affine algebraic groups is an isogeny when its underlying
scheme morphism is finite, flat, and surjective. -/
def IsIsogeny {G H : AffineAlgebraicGroup K} (f : G.1 ⟶ H.1) : Prop :=
  IsFinite f.hom.hom.left ∧
    Flat f.hom.hom.left ∧
    Surjective f.hom.hom.left

end LeanCategories.AlgebraicGeometry
