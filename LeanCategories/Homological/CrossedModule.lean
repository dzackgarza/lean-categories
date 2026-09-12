/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Crossed modules of groups

Weibel, *An Introduction to Homological Algebra* (1994), §6.6, pp. 182--188
(FC05-C06-U077).

A crossed module is a homomorphism `∂ : N → E` together with an action of `E`
on `N` satisfying the two Peiffer identities.  This file records exactly that
definition.  Equivalence of crossed modules and the associated `H³` class are
separate source units.
-/

@[expose] public section

namespace LeanCategories.Homological

universe uN uE

/-- A crossed module `N → E`: a group homomorphism, an action of `E` on `N`,
and the two Peiffer identities.

Source: Weibel, §6.6, pp. 182--188 (FC05-C06-U077). -/
structure CrossedModule (N : Type uN) (E : Type uE) [Group N] [Group E] where
  /-- The boundary homomorphism `∂ : N → E`. -/
  boundary : N →* E
  /-- The action of `E` on `N` by automorphisms. -/
  action : E →* MulAut N
  /-- First Peiffer identity: `∂m` acts on `N` by conjugation by `m`. -/
  boundary_action : ∀ m n : N,
    action (boundary m) n = m * n * m⁻¹
  /-- Equivariance of the boundary under the action and conjugation in `E`. -/
  action_boundary : ∀ e : E, ∀ n : N,
    boundary (action e n) = e * boundary n * e⁻¹

namespace CrossedModule

variable {N : Type uN} {E : Type uE} [Group N] [Group E]

/-- The action associated to a crossed module, as an explicit function. -/
def act (X : CrossedModule N E) (e : E) (n : N) : N :=
  X.action e n

@[simp]
theorem boundary_act (X : CrossedModule N E) (e : E) (n : N) :
    X.boundary (X.act e n) = e * X.boundary n * e⁻¹ :=
  X.action_boundary e n

@[simp]
theorem boundary_act_self (X : CrossedModule N E) (m n : N) :
    X.act (X.boundary m) n = m * n * m⁻¹ :=
  X.boundary_action m n

end CrossedModule

end LeanCategories.Homological
