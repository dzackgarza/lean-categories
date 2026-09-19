/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Basic

@[expose] public section

/-!
# Partial ring-homomorphism graphs

Definition-level transcription of Atiyah--Macdonald FC04-C05-U031, following the
`ChevalleyHom` representation in the FLT reference.  A partial homomorphism from a field
`L` to a field `Ω` is represented by its graph as a subring of `L × Ω`; `Above Γ₀`
records graph extensions of a supplied initial graph.

The Zorn/maximal-extension statement is not part of this file.
-/

namespace LeanCategories.Algebra.ChevalleyHom

universe u v

variable {L : Type u} {Ω : Type v} [Field L] [Field Ω]

/-- A subring of `L × Ω` is graph-like when the only element over `0 : L` has second
coordinate zero. -/
def IsGraph (Γ : Subring (L × Ω)) : Prop :=
  ∀ a : Ω, ((0 : L), a) ∈ Γ → a = 0

/-- The graph of a ring homomorphism whose domain is a subring of `L`. -/
def graph (R : Subring L) (φ : R →+* Ω) : Subring (L × Ω) :=
  ((R.subtype).prod φ).range

/-- Graph-like subrings extending a supplied initial graph. -/
def Above (Γ₀ : Subring (L × Ω)) : Set (Subring (L × Ω)) :=
  {Γ | Γ₀ ≤ Γ ∧ IsGraph Γ}

end LeanCategories.Algebra.ChevalleyHom
