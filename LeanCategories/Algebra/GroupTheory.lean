/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.CategoryTheory.Action
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Standard group-theory routes

Mathlib owns the standard group constructions used by the Dummit--Foote
catalogue. This module gives the project a stable owner and project-facing
names without introducing parallel definitions.

The subgroup lattice is the preorder category on `Subgroup G`. Actions use
Mathlib's action functor and action category. Quotients, automorphisms,
products, free groups, presentations, and standard examples remain their
Mathlib objects.
-/

@[expose] public section

namespace LeanCategories.Algebra

open CategoryTheory

universe u v

section Subgroups

variable (G : Type u) [Group G]

/-! ### Subgroups and quotient groups -/

/** The subgroup lattice, regarded as its canonical preorder category. */
abbrev SubgroupCat : Type (u + 1) := Cat.of (Subgroup G)

/** The canonical subgroup inclusion morphism. */
abbrev subgroupInclusion {H K : Subgroup G} (h : H ≤ K) :
    (H : SubgroupCat G) ⟶ K := h

/** The quotient group by a normal subgroup. */
abbrev quotientGroup (N : Subgroup G) [N.Normal] : Type u := G ⧸ N

/** The canonical quotient homomorphism. */
abbrev quotientGroupMap (N : Subgroup G) [N.Normal] : G →* quotientGroup G N :=
  QuotientGroup.mk' N

/** The centralizer of a set. */
abbrev centralizer (s : Set G) : Subgroup G := Subgroup.centralizer s

/** The normalizer of a set. */
abbrev normalizer (s : Set G) : Subgroup G := Subgroup.normalizer s

/** The left coset of a subgroup. */
abbrev leftCoset (H : Subgroup G) (g : G) : Set G := g • (H : Set G)

/** The right coset of a subgroup. */
abbrev rightCoset (H : Subgroup G) (g : G) : Set G :=
  MulOpposite.op g • (H : Set G)

/** The index of a subgroup, with zero denoting infinite index. */
abbrev subgroupIndex (H : Subgroup G) : ℕ := H.index

end Subgroups

section GroupInvariants

variable (G : Type u) [Group G]

/-! ### Basic group invariants and properties -/

/** The cardinality of a group, when finite. */
abbrev groupOrder : ℕ := Nat.card G

/** The order of an element, with zero denoting infinite order. */
abbrev elementOrder (g : G) : ℕ := orderOf g

/** The cyclic-group predicate. */
abbrev isCyclicGroup : Prop := IsCyclic G

/** The simple-group predicate. */
abbrev isSimpleGroup : Prop := IsSimpleGroup G

/** The finitely-generated-group predicate. */
abbrev isFinitelyGeneratedGroup : Prop := Group.FG G

/** The torsion-group predicate. */
abbrev isTorsionGroup : Prop := Monoid.IsTorsion G

/** The p-group predicate. */
abbrev isPGroup (p : ℕ) : Prop := IsPGroup p G

/** The nilpotent-group predicate. */
abbrev isNilpotentGroup : Prop := Group.IsNilpotent G

/** The solvable-group predicate. */
abbrev isSolvableGroup : Prop := IsSolvable G

/** The upper central series of a group. */
abbrev upperCentralSeriesOfGroup (n : ℕ) : Subgroup G := upperCentralSeries G n

/** The derived series of a group. */
abbrev derivedSeriesOfGroup (n : ℕ) : Subgroup G := derivedSeries G n

end GroupInvariants

section Actions

variable (M : Type u) [Monoid M] (X : Type v) [MulAction M X]

/-! ### Actions -/

/** The functor represented by an action. */
abbrev actionFunctor : SingleObj M ⥤ Type v :=
  CategoryTheory.actionAsFunctor M X

/** The category of elements of an action. */
abbrev actionCategory : Type v :=
  CategoryTheory.ActionCategory M X

variable {X}

/** The orbit of a point under an action. */
abbrev orbit (x : X) : Set X := MulAction.orbit M x

end Actions

section GroupActions

variable (G : Type u) [Group G] (X : Type v) [MulAction G X]

/** The action groupoid for a group action. */
abbrev actionGroupoid : Type v :=
  CategoryTheory.ActionCategory G X

/** The stabilizer of a point. */
abbrev stabilizer (x : X) : Subgroup G := MulAction.stabilizer G x

/** The permutation representation associated to a group action. */
abbrev permutationRepresentation : G →* Equiv.Perm X := MulAction.toPermHom G X

end GroupActions

section Automorphisms

variable (G : Type u) [Group G]

/-! ### Automorphisms and standard actions -/

/** The automorphism group of a group. */
abbrev groupAutomorphism : Type u := MulAut G

/** The canonical inner-automorphism homomorphism. */
abbrev innerAutomorphism : G →* groupAutomorphism G := MulAut.conj

end Automorphisms

section Products

variable (G : Type u) [Group G] (H : Type v) [Group H]

/-! ### Products -/

/** The direct product of two groups. */
abbrev directProduct : Type (max u v) := G × H

/** The canonical direct-product homomorphism. */
abbrev directProductMap {K : Type*} [Group K] (f : K →* G) (g : K →* H) :
    K →* directProduct G H := MonoidHom.prod f g

end Products

section SemidirectProducts

variable (G : Type u) [Group G] (N : Type v) [Group N]

/** The semidirect product determined by an action homomorphism. */
abbrev semidirectProduct (phi : G →* MulAut N) : Type (max u v) :=
  SemidirectProduct phi

end SemidirectProducts

section FreeAndPresented

variable (alpha : Type u)

/-! ### Free groups and group presentations -/

/** The free group on a type of generators. */
abbrev freeGroup : Type u := FreeGroup alpha

/** The group presented by generators `alpha` and free-group relations `rels`. */
abbrev presentedGroup (rels : Set (FreeGroup alpha)) : Type u :=
  PresentedGroup rels

/** The canonical generator map into a presented group. */
abbrev presentedGenerator (rels : Set (FreeGroup alpha)) :
    alpha → presentedGroup alpha rels := PresentedGroup.of

end FreeAndPresented

section StandardExamples

/-! ### Standard examples -/

/** The symmetric group on a type. */
abbrev symmetricGroup (alpha : Type u) : Type u := Equiv.Perm alpha

/** The dihedral group of parameter `n`. */
abbrev dihedralGroup (n : ℕ) : Type := DihedralGroup n

/** The quaternion group of parameter `n`. */
abbrev quaternionGroup (n : ℕ) : Type := QuaternionGroup n

end StandardExamples

section LinearGroups

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-! ### General linear groups -/

/** The general linear group of an `R`-module. */
abbrev generalLinearGroup : Type v := LinearMap.GeneralLinearGroup R M

end LinearGroups

end LeanCategories.Algebra
