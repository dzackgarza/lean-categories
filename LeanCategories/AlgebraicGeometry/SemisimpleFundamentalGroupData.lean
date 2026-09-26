/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Semisimple fundamental-group data

Definition-level realization of Humphreys FC16-C11-U003.

The ambient additive group `Λ` is the abstract weight lattice supplied by
FC16-C11-U002.  The actual maximal-torus character lattice `X(T)` and the
root lattice `Λ_r` are supplied as additive subgroups of `Λ`.  With those
source data in hand, Humphreys' fundamental group and the simply-connected
and adjoint type predicates are ordinary quotient/equality constructions.

Producing the embeddings `Λ_r ≤ X(T) ≤ Λ` from an arbitrary semisimple
algebraic group is theorem-level bridge work and is deliberately not part of
these definitions.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

universe u


variable {Λ : Type u} [AddCommGroup Λ]

/-- Humphreys' fundamental group `π(G) = Λ / X(T)`, once the character
lattice has been supplied as a subgroup of the abstract weight lattice. -/
def semisimpleFundamentalGroup (characterLattice : AddSubgroup Λ) : Type u :=
  Λ ⧸ characterLattice

/-- A semisimple group is of simply connected (universal) type when its
character lattice is the full abstract weight lattice. -/
def IsSimplyConnectedType (characterLattice : AddSubgroup Λ) : Prop :=
  characterLattice = ⊤

/-- A semisimple group is of adjoint type when its character lattice is
exactly the root lattice. -/
def IsAdjointType
    (rootLattice characterLattice : AddSubgroup Λ) : Prop :=
  characterLattice = rootLattice

/-- Humphreys' complete type datum attached to the abstract weight, root, and
character lattices: the fundamental group together with the simply-connected
and adjoint-type conditions. -/
structure SemisimpleFundamentalGroupData
    (rootLattice characterLattice : AddSubgroup Λ) where
  fundamentalGroup : Type u
  simplyConnected : Prop
  adjoint : Prop

/-- Construct the fundamental group and the two type conditions from the
source lattice data. -/
def semisimpleFundamentalGroupData
    (rootLattice characterLattice : AddSubgroup Λ) :
    SemisimpleFundamentalGroupData rootLattice characterLattice where
  fundamentalGroup := semisimpleFundamentalGroup characterLattice
  simplyConnected := IsSimplyConnectedType characterLattice
  adjoint := IsAdjointType rootLattice characterLattice

end LeanCategories.AlgebraicGeometry
