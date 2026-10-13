/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-!
# Abstract Jordan parts in a semisimple Lie algebra

This file records the definition in Humphreys, *Introduction to Lie Algebras and
Representation Theory*, Section 5.4, p. 24 (FC14-C02-U025). For an element `x` of a
finite-dimensional semisimple Lie algebra, its abstract semisimple and nilpotent parts are the
elements whose adjoint actions form the ordinary Jordan decomposition of `ad x`.

Valid abstract-Jordan data are pairs satisfying the intrinsic predicate.
Existence and uniqueness are separate results about semisimple Lie algebras;
no arbitrary pair is selected before those results.
-/

noncomputable section

namespace LeanCategories.LieAlgebra

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L]

/-- The source predicate characterizing the abstract Jordan parts of `x`.

The first component is the ad-semisimple part and the second is the ad-nilpotent part. The
equations say that they sum to `x` and commute in the Lie algebra; their adjoint endomorphisms
therefore give the ordinary Jordan decomposition of `ad x`. -/
def IsAbstractJordanPair [CharZero K] [IsAlgClosed K] [FiniteDimensional K L]
    [LieAlgebra.IsSemisimple K L] (x : L) (parts : L × L) : Prop :=
  x = parts.1 + parts.2 ∧
    ⁅parts.1, parts.2⁆ = 0 ∧
    (LieAlgebra.ad K L parts.1).IsSemisimple ∧
    IsNilpotent (LieAlgebra.ad K L parts.2)

/-- Source-faithful abstract Jordan pair data: a pair together with Humphreys'
intrinsic characterization. -/
abbrev AbstractJordanPairData [CharZero K] [IsAlgClosed K] [FiniteDimensional K L]
    [LieAlgebra.IsSemisimple K L] (x : L) :=
  {parts : L × L // IsAbstractJordanPair K L x parts}

/-- The abstract ad-semisimple part of `x`. -/
def abstractSemisimplePart [CharZero K] [IsAlgClosed K] [FiniteDimensional K L]
    [LieAlgebra.IsSemisimple K L] {x : L} (D : AbstractJordanPairData K L x) : L :=
  D.1.1

/-- The abstract ad-nilpotent part of `x`. -/
def abstractNilpotentPart [CharZero K] [IsAlgClosed K] [FiniteDimensional K L]
    [LieAlgebra.IsSemisimple K L] {x : L} (D : AbstractJordanPairData K L x) : L :=
  D.1.2

end LeanCategories.LieAlgebra
