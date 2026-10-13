/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# Essential module extensions

Definition-level realization of Matsumura FC13-CB-U022.

For an extension `M ⊆ L`, essentiality means that every nonzero submodule
of `L` meets `M` nontrivially. The source's equivalent elementwise
characterization by nonzero scalar multiples is a result about this
predicate and is not included in Sweep III.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v

variable {R : Type u} {L : Type v}
  [CommRing R] [AddCommGroup L] [Module R L]

/-- Matsumura Appendix B: a submodule `M ⊆ L` is an essential extension
when every nonzero submodule of `L` has nonzero intersection with `M`.

This is FC13-CB-U022. -/
def IsEssentialExtension (M : Submodule R L) : Prop :=
  ∀ N : Submodule R L, N ≠ ⊥ → N ⊓ M ≠ ⊥

end LeanCategories.Algebra
