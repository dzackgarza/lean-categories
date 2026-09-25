/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.SplitOctonionData
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Derivation data for the split Cayley algebra

Definition-level realization of Humphreys FC14-C05-U041.

For a trace-zero three-by-three matrix x, Humphreys writes the explicit
endomorphism

  [[a,v],[w,b]] |-> [[0,xv],[-x^t w,0]].

He then verifies that these maps are derivations, form a faithful copy of
sl(3), and that the diagonal trace-zero copy gives a two-dimensional
self-centralizing subalgebra.

The split-octonion owner deliberately carries only the source multiplication
formula, not proof-bearing algebra instances.  This file therefore records
the corresponding raw linearity/Leibniz predicates and the exact displayed
matrix formula.  No derivation, representation, Lie-subalgebra, faithfulness,
dimension, or self-centrality theorem is proved in Sweep III.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable (K : Type u) [Field K]

/-- Componentwise addition on the raw Zorn-matrix carrier. -/
def splitOctonionAddData
    (x y : SplitOctonionData K) : SplitOctonionData K :=
  ⟨x.a + y.a, x.b + y.b, x.v + y.v, x.w + y.w⟩

/-- Componentwise scalar multiplication on the raw Zorn-matrix carrier. -/
def splitOctonionSmulData
    (r : K) (x : SplitOctonionData K) : SplitOctonionData K :=
  ⟨r * x.a, r * x.b, r • x.v, r • x.w⟩

/-- The source linearity predicate for a raw endomorphism of the split
octonion carrier. -/
def IsSplitOctonionLinearData
    (d : SplitOctonionData K → SplitOctonionData K) : Prop :=
  (∀ x y,
    d (splitOctonionAddData K x y) =
      splitOctonionAddData K (d x) (d y)) ∧
  (∀ r x,
    d (splitOctonionSmulData K r x) =
      splitOctonionSmulData K r (d x))

/-- Raw derivation predicate for Humphreys' Cayley multiplication. -/
def IsSplitOctonionDerivationData
    (d : SplitOctonionData K → SplitOctonionData K) : Prop :=
  IsSplitOctonionLinearData K d ∧
  ∀ x y,
    d (SplitOctonionData.mul x y) =
      splitOctonionAddData K
        (SplitOctonionData.mul x (d y))
        (SplitOctonionData.mul (d x) y)

/-- Raw carrier of derivations, defined by the exact source predicate rather
than a proof-bearing nonassociative-algebra instance. -/
abbrev SplitOctonionDerivationData :=
  {d : SplitOctonionData K → SplitOctonionData K //
    IsSplitOctonionDerivationData K d}

/-- Matrix carrier for sl(3,K), at the definition boundary needed here. -/
abbrev CayleySl3MatrixData :=
  {x : Matrix (Fin 3) (Fin 3) K // Matrix.trace x = 0}

/-- Humphreys' displayed raw action of a trace-zero matrix on a split
octonion. -/
def cayleySl3RawDerivationData
    (x : CayleySl3MatrixData K) :
    SplitOctonionData K → SplitOctonionData K :=
  fun c =>
    ⟨0, 0,
      Matrix.mulVec x.1 c.v,
      -(Matrix.mulVec x.1.transpose c.w)⟩

/-- Exact graph for the proposed embedding sl(3,K) -> Der(C). -/
def IsCayleySl3DerivationData
    (x : CayleySl3MatrixData K)
    (d : SplitOctonionDerivationData K) : Prop :=
  d.1 = cayleySl3RawDerivationData K x

/-- Graph predicate for a proposed derivation-valued realization of the
displayed sl(3)-action.

Existence, uniqueness, injectivity and bracket compatibility are theorem-layer
properties. -/
def IsCayleySl3DerivationMapData
    (delta : CayleySl3MatrixData K → SplitOctonionDerivationData K) : Prop :=
  ∀ x, IsCayleySl3DerivationData K x (delta x)

/-- The diagonal trace-zero matrices used by Humphreys for H. -/
abbrev CayleyDiagonalSl3Data :=
  {x : CayleySl3MatrixData K //
    ∀ i j : Fin 3, i ≠ j → x.1 i j = 0}

/-- Exact graph of the diagonal part H inside the raw sl(3)-derivation
construction. -/
def IsCayleyDiagonalDerivationData
    (x : CayleyDiagonalSl3Data K)
    (d : SplitOctonionDerivationData K) : Prop :=
  IsCayleySl3DerivationData K x.1 d

end LeanCategories.Algebra
