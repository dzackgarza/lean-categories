/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Class-formation conjugation data

Definition-level realization of the raw formulas in Serre FC10-C11-U007.
Restriction to the appropriate formation subgroups and fixed coefficient
modules, compatibility, and the resulting transported cohomology
isomorphisms are result-layer statements.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable (G : Type u) (A : Type v)
variable [Group G] [SMul G A]

/-- Serre's conjugation formula `t ↦ s⁻¹ t s` (FC10-C11-U007). -/
def serreFormationConjugationData (s t : G) : G :=
  s⁻¹ * t * s

/-- Serre's coefficient-transport formula `a ↦ s • a`
(FC10-C11-U007). -/
def serreFormationCoefficientTransportData (s : G) (a : A) : A :=
  s • a

end LeanCategories.Homological
