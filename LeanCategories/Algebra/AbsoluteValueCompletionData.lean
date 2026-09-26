/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Absolute-value completion notation data

Definition-level realization of Neukirch FC09-C02-U094.

For a real-valued absolute value `v` on a field `K`, Neukirch writes
`K_v` for the completion, `bar K_v` for an algebraic closure of that
completion, again writes `v` for the canonical absolute value on `K_v`,
and writes `bar v` for its unique extension to `bar K_v`.

Mathlib already owns both `v.Completion` and the canonical
`AlgebraicClosure` construction.  The completion absolute value is simply
the norm absolute value of the completed normed field, exactly as in the
mapped reference implementation.

Sweep III does not prove the algebraic-extension theorem.  Instead it records
the source's defining restriction predicate and treats the closure absolute
value as data carrying that predicate.  Existence and uniqueness remain
result-layer obligations; no arbitrary absolute value is selected beforehand.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

variable {K : Type u} [Field K]

/-- Neukirch's notation `K_v`: the completion of `K` at the real-valued
absolute value `v`. -/
abbrev absoluteValueCompletionData (v : AbsoluteValue K ℝ) : Type u :=
  v.Completion

/-- Neukirch's notation `bar K_v`: the canonical algebraic closure of the
completion at `v`. -/
abbrev absoluteValueCompletionClosureData
    (v : AbsoluteValue K ℝ) : Type u :=
  AlgebraicClosure (absoluteValueCompletionData v)

/-- The canonical extension of `v` to `K_v`, represented by the norm
absolute value on the completed normed field.

Agreement with `v` on the dense copy of `K` is a comparison theorem, not
part of this definition. -/
def completionAbsoluteValueData
    (v : AbsoluteValue K ℝ) :
    AbsoluteValue (absoluteValueCompletionData v) ℝ :=
  NormedField.toAbsoluteValue (absoluteValueCompletionData v)

/-- Intrinsic restriction condition characterizing an absolute value on
`bar K_v` as an extension of the canonical value on `K_v`. -/
def IsCompletionClosureAbsoluteValueData
    (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue (absoluteValueCompletionClosureData v) ℝ) : Prop :=
  ∀ x : absoluteValueCompletionData v,
    w (algebraMap (absoluteValueCompletionData v)
      (absoluteValueCompletionClosureData v) x) =
      completionAbsoluteValueData v x

/-- Source-faithful data for Neukirch's `bar v`: an absolute value on the
algebraic closure together with the exact restriction condition to the
completion.  Existence and uniqueness are supplied later by the algebraic
extension theorem. -/
abbrev CompletionClosureAbsoluteValueData (v : AbsoluteValue K ℝ) :=
  {w : AbsoluteValue (absoluteValueCompletionClosureData v) ℝ //
    IsCompletionClosureAbsoluteValueData v w}

end LeanCategories.Algebra
