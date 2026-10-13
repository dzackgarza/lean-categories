/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Recursive root recovery from a Cartan matrix

Definition-level realization of Humphreys FC14-C03-U038.

Write a positive root in simple-root coordinates.  Once all roots through a
given height are known, the root string through a root `beta` in the direction
of a simple root `alpha_i` determines whether `beta + alpha_i` occurs: if
`p` is the already visible backward-string length, then

`q = p - <beta, alpha_i>`.

The next root occurs exactly when `q > 0`.  The Cartan matrix computes the
displayed pairing from the simple-root coordinates.  This file records that
recursive construction only.  Correctness, finiteness, and identification of
the recovered set with an ambient root system are theorem content.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Algebra

universe u

/-- Integer coordinates relative to an ordered set of simple roots. -/
abbrev CartanRootCoordinates (ι : Type u) := ι → ℤ

/-- The `i`th simple root in simple-root coordinates. -/
def cartanSimpleRoot {ι : Type u} [DecidableEq ι] (i : ι) : CartanRootCoordinates ι :=
  fun j => if j = i then 1 else 0

/-- Height of a vector in simple-root coordinates. -/
def cartanRootHeight {ι : Type u} [Fintype ι] (beta : CartanRootCoordinates ι) : ℤ :=
  ∑ j, beta j

/-- The Cartan integer `<beta, alpha_i>`, computed from the coordinates of
`beta` and the Cartan matrix of the ordered simple roots. -/
def cartanPairingWithSimple {ι : Type u} [Fintype ι]
    (A : Matrix ι ι ℤ) (beta : CartanRootCoordinates ι) (i : ι) : ℤ :=
  ∑ j, beta j * A j i

/-- Subtract `k` copies of the `i`th simple root from a coordinate vector. -/
def cartanSubtractSimple {ι : Type u} [DecidableEq ι]
    (beta : CartanRootCoordinates ι) (i : ι) (k : ℕ) : CartanRootCoordinates ι :=
  fun j => beta j - (k : ℤ) * if j = i then 1 else 0

/-- The part of the backward `alpha_i`-string already present in the roots
recovered at lower heights.  The coordinate `beta_i` gives a finite search
bound for positive-root coordinates. -/
def cartanBackwardStringLength {ι : Type u} [Fintype ι] [DecidableEq ι]
    (known : Finset (CartanRootCoordinates ι))
    (beta : CartanRootCoordinates ι) (i : ι) : ℕ :=
  ((Finset.range (Int.toNat (beta i) + 1)).filter fun k =>
      cartanSubtractSimple beta i k ∈ known).sup id

/-- Root-string test for adjoining `beta + alpha_i` from the roots already
known at lower heights. -/
def cartanCanExtendRoot {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (known : Finset (CartanRootCoordinates ι))
    (beta : CartanRootCoordinates ι) (i : ι) : Prop :=
  (cartanBackwardStringLength known beta i : ℤ) - cartanPairingWithSimple A beta i > 0

/-- One height step of Humphreys' Cartan-matrix root-recovery algorithm.

At height zero this seeds the simple roots.  At later stages it extends exactly
the roots of the current height using the root-string test. -/
def cartanRootRecoveryStep {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (height : ℕ)
    (known : Finset (CartanRootCoordinates ι)) : Finset (CartanRootCoordinates ι) := by
  classical
  if height = 0 then
    exact Finset.univ.image cartanSimpleRoot
  else
    exact known ∪
      (known.filter fun beta => cartanRootHeight beta = (height : ℤ)).biUnion fun beta =>
        (Finset.univ.filter fun i => cartanCanExtendRoot A known beta i).image fun i =>
          beta + cartanSimpleRoot i

/-- Positive roots recovered through the indicated height-recursion stage. -/
def cartanRecoveredPositiveRootsUpTo {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) : ℕ → Finset (CartanRootCoordinates ι)
  | 0 => ∅
  | n + 1 => cartanRootRecoveryStep A n (cartanRecoveredPositiveRootsUpTo A n)

/-- The positive-root set produced by the full height recursion. -/
def cartanRecoveredPositiveRoots {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) : Set (CartanRootCoordinates ι) :=
  {beta | ∃ n, beta ∈ cartanRecoveredPositiveRootsUpTo A n}

/-- The signed root set obtained after recovering the positive roots. -/
def cartanRecoveredRoots {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) : Set (CartanRootCoordinates ι) :=
  {beta | beta ∈ cartanRecoveredPositiveRoots A ∨ -beta ∈ cartanRecoveredPositiveRoots A}

end LeanCategories.Algebra
