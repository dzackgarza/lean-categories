/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpFoldEvenOnFixed

/-!
# Probe: the fold pairs evenly with the invariant part

`FoldingTdpE8FoldNotRoot.lean` showed the folded `E₈` root is not a root of `T_dP`. The half left as
prose was that it *is* a root of the fixed lattice `M^σ`, which for square `(−4)` means exactly that
its pairings with the invariant part are even. The probes here decide that.

The second probe is the guard: the shape lemma says an invariant vector's second `E₈` block is minus
its first, which is what makes the two block contributions equal. Without it the evenness would be
accidental rather than structural.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- An invariant vector has second block minus first. -/
example {x : TdpIndex → ℤ} (h : tdpSwapSign x = x) (j : Fin 8) :
    x (Sum.inr (Sum.inr j)) = -x (Sum.inr (Sum.inl j)) :=
  tdpSwapSign_fixed_second_eq_neg_first h j

/-- The fold pairs evenly with every invariant vector. -/
example (i : Fin 8) {z : TdpIndex → ℤ} (hz : tdpSwapSign z = z) :
    ∃ k : ℤ,
      Matrix.toBilin' tdpBlockGram (foldedVector tdpIsometry (tdpE8Root i)) z = 2 * k :=
  tdpFoldedE8Root_toBilin_fixed i hz

end LeanCategories.Lattices.Valued
