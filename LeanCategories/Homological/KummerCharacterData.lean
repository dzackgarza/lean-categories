/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Raw Kummer-character data

Definition-level realization of the representative formula in Serre,
*Local Fields*, Chapter XIV, `FC10-C14-U008`.

Given `a` in the base field and a chosen `n`-th root `α` in a Galois ambient
field, Serre first forms the ratio `σ(α) / α`.  Proving that this ratio lies in
the `n`-th roots of unity, identifying those roots with `ZMod n` via a chosen
primitive root, and proving the resulting function is a character are
result-layer statements.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]

/-- Raw predicate saying that `α` is a chosen `n`-th root of the base element
`a`.  It is a predicate rather than proof-bearing constructor data. -/
def IsSerreKummerRootData (n : ℕ) (a : K) (α : L) : Prop :=
  α ^ n = algebraMap K L a

/-- Serre's Kummer root-ratio representative `σ(α) / α`
(FC10-C14-U008). -/
def serreKummerRootRatioData (α : L) (σ : L ≃ₐ[K] L) : L :=
  σ α / α

/-- The raw function of Galois automorphisms obtained from a chosen Kummer
root.  Its root-of-unity range and homomorphism law are not bundled here. -/
def serreKummerRootRatioFunctionData (α : L) : (L ≃ₐ[K] L) → L :=
  fun σ => serreKummerRootRatioData α σ

end LeanCategories.Homological
