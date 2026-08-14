/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.CategoryTheory.Action
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SemidirectProduct

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

end Subgroups

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

end LeanCategories.Algebra
