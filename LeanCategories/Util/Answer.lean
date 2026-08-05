/-
Re-exports the `answer(...)` elaborator provided by the `aiReviewCiLean` dependency
(shipped with ai-review-ci). Because it arrives as a dependency, its internals live
under `.lake/packages` and are invisible to this repo's QC gate.

`answer(e)` marks the *answer* to a problem as distinct from its *proof*, tagging `e`
with an `answer` annotation. When a `Prop` is expected and the answer is left as the
unproved-proof token, it elaborates to `True` — a gate-legal "answer not yet
determined" for the conjecture ledger (#21) and the experimental-unverified backend
status (#28). That unknown-answer form uses the banned token, so it belongs in the
excluded conjecture surfaces (`**/*.conjecture*`, `**/Conjectures/**`); this module
only re-exports the elaborator and smoke-tests the concrete forms.
-/
module

public import AiReviewCi.Answer

@[expose] public section

open AiReviewCi.Answer

/-- `answer(e)` for a concrete proposition carries the underlying claim. -/
example : answer(2 + 2 = 4) := by decide

/-- `answer(e)` at a data type elaborates the concrete value. -/
example : (answer(5) : Nat) = 5 := rfl
