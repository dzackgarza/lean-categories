/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Split Cayley/octonion source data

Definition-level realization of Humphreys FC14-C05-U040, following the
Zorn-vector-matrix model in the pinned TauCeti reference.  Only the carrier,
displayed multiplication, distinguished unit datum, trace, and trace-zero
carrier are recorded here.  Algebra laws and dimension statements are result
content and are deliberately not bundled into this file.
-/

@[expose] public section

namespace LeanCategories.Algebra

open Matrix

/-- The Zorn-vector-matrix carrier `[[a,v],[w,b]]` of the split Cayley algebra. -/
@[ext]
structure SplitOctonionData (R : Type*) where
  a : R
  b : R
  v : Fin 3 → R
  w : Fin 3 → R

namespace SplitOctonionData

variable {R : Type*}

/-- The distinguished unit datum `[[1,0],[0,1]]`. -/
def one [Zero R] [One R] : SplitOctonionData R :=
  ⟨1, 1, 0, 0⟩

/-- Humphreys' Zorn-vector-matrix multiplication formula. -/
def mul [CommRing R] (x y : SplitOctonionData R) : SplitOctonionData R :=
  ⟨x.a * y.a + x.v ⬝ᵥ y.w,
    x.b * y.b + x.w ⬝ᵥ y.v,
    x.a • y.v + y.b • x.v - x.w ⨯₃ y.w,
    y.a • x.w + x.b • y.w + x.v ⨯₃ y.v⟩

/-- The vector-matrix trace `a+b`. -/
def trace [Add R] (x : SplitOctonionData R) : R :=
  x.a + x.b

/-- The source carrier `C₀` of trace-zero split octonions. -/
def traceZero [Add R] [Zero R] : Set (SplitOctonionData R) :=
  {x | trace x = 0}

end SplitOctonionData

end LeanCategories.Algebra
