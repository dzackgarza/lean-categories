/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Lie.Derivation.Basic

/-!
# Locally nilpotent exponential data

Definition-level realization of Humphreys FC14-C05-U029.

Over a characteristic-zero field, an endomorphism is locally nilpotent when
each vector is killed by some power.  Humphreys defines its exponential by the
finite series

  exp(f)(v) = sum_{i < n} f^i(v) / i!

for any bound n with f^n(v)=0, and then proves that these pointwise finite
series patch to a linear automorphism.

Sweep III records the local-nilpotence predicate and the exact graph of that
finite-series prescription.  It does not prove independence of the chosen
bound, additivity, scalar compatibility, bijectivity, or the inverse formula
exp(-f).
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Algebra

universe u v

variable (K : Type u) (V : Type v)
variable [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- Humphreys' pointwise definition of a locally nilpotent endomorphism. -/
def IsLocallyNilpotentEndomorphismData
    (f : Module.End K V) : Prop :=
  ∀ v : V, ∃ n : ℕ, (f ^ n) v = 0

/-- Exact graph of the locally finite exponential series at one vector.

The truncation bound is part of the existential witness; no independence from
that witness is proved here. -/
def IsLocallyNilpotentExponentialValueData
    (f : Module.End K V) (v w : V) : Prop :=
  ∃ n : ℕ,
    (f ^ n) v = 0 ∧
    w = ∑ i ∈ Finset.range n,
      ((Nat.factorial i : K)⁻¹) • ((f ^ i) v)

/-- Graph predicate for a proposed exponential function of a locally
nilpotent endomorphism.

Once the result layer proves the pointwise graph single-valued and compatible
with the module operations, this function packages as the source linear
automorphism. -/
def IsLocallyNilpotentExponentialData
    (f : Module.End K V) (e : V → V) : Prop :=
  IsLocallyNilpotentEndomorphismData K V f ∧
  ∀ v : V, IsLocallyNilpotentExponentialValueData K V f v (e v)

end LeanCategories.Algebra
