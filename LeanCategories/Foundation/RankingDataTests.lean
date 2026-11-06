/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.Sets
public import Mathlib.Tactic.FinCases

/-!
# Rankings and encodings are distinct selected data (#96)

On the same carrier, a pre-existing encoding and an encoding derived from a selected ranking need
not agree, and the ranking-derived one does not replace the earlier selection. This is the compiled
control for that: two selections on `Bool`, differing at `true`.

The pre-existing encoding sends `true ↦ 0`, `false ↦ 1`; the selected ranking is the reverse
standard ranking `true ↦ 1`, `false ↦ 0`, whose derived encoding inherits that order. No monotone
comparison between the two induced orders is claimed — only that they differ.
-/

@[expose] public section

namespace LeanCategories.Foundation

/-- The pre-existing selected encoding on `Bool`: `true` first. -/
def boolEncodingTrueFirst : Encodable Bool where
  encode b := if b then 0 else 1
  decode n := some (if n = 0 then true else false)
  encodek b := by cases b <;> simp

/-- The selected ranking on `Bool`: the reverse standard ranking, `true ↦ 1`, `false ↦ 0`. -/
def boolReverseRanking : RankingData Bool (Fin 2) where
  rank :=
    { toFun := fun b => if b then 1 else 0
      invFun := fun n => decide (n = 1)
      left_inv := by intro b; cases b <;> decide
      right_inv := by
        intro n
        fin_cases n <;> decide }

/-- Under the pre-existing encoding, `true` precedes `false`. -/
theorem boolEncodingTrueFirst_true_before_false :
    boolEncodingTrueFirst.encode true < boolEncodingTrueFirst.encode false := by decide

/-- Under the selected ranking, `false` precedes `true` — the opposite order on the same carrier. -/
theorem boolReverseRanking_le_false_true : boolReverseRanking.le false true := by
  simp [RankingData.le, boolReverseRanking]

/-- The selected ranking is not the order induced by the pre-existing encoding: the two disagree on
the pair `(false, true)`. A ranking is selected data, and a different encoding already present on the
carrier neither determines it nor is replaced by it. -/
theorem boolRanking_not_preexisting_order :
    boolReverseRanking.le false true ∧
      ¬ (boolEncodingTrueFirst.encode false < boolEncodingTrueFirst.encode true) := by
  refine ⟨boolReverseRanking_le_false_true, ?_⟩
  decide

/-- The ranking's inverse recovers the element at a selected index. -/
theorem boolReverseRanking_unrank_one : boolReverseRanking.unrank 1 = true := by
  simp [RankingData.unrank, boolReverseRanking]

/-- The ranking's index map and inverse are mutual inverses on a concrete element. -/
theorem boolReverseRanking_rank_unrank :
    boolReverseRanking.rank (boolReverseRanking.unrank 0) = 0 :=
  boolReverseRanking.rank_unrank 0

end LeanCategories.Foundation
