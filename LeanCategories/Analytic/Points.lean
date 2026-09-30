/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.Subsets
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-!
# Points of `ℂ`, `ℝ`, and of function spaces

The complex plane is one object; its real and imaginary parts, conjugation and modulus are not
invariant under its (wild) field automorphisms, so they are operations on the points of that one
object: functors out of the discrete category `Discrete ℂ` (any function on a discrete category is
one). `ℝ ⊆ ℂ` is `realToComplex`. Operations:

* `re`, `im`, `conj`, `abs`;
* `approximations z`: `ε ↦` the Gaussian rationals `a + b i` within `ε` of `z` — the answers a
  decimal approximation may give.

Functions are the points of `Discrete (Σ A B, A → B)`; `image` sends `f : A → B` to the subset
`range f ↪ B`. Real functions `ℝ → ℝ` are the points of `Discrete (ℝ → ℝ)`, with:

* `limits f`: `a ↦` the extended reals `L` with `f → L` at `a` (`a ∈ EReal`: `±∞` are the filters
  `atTop`/`atBot`, a real `a` the punctured neighbourhood filter);
* `integral f`: `(a, b) ↦ ∫ x in a..b, f x`;
* `taylor f`: `n ↦` the degree-`n` Taylor polynomial of `f` at `0`,
  `∑_{k ≤ n} f⁽ᵏ⁾(0)/k! · Xᵏ`.
-/

open CategoryTheory Filter Topology Polynomial

namespace LeanCategories.Analytic

universe u

noncomputable section

/-- Points of `ℂ`. -/
abbrev ComplexPoints := Discrete ℂ
/-- Points of `ℝ`. -/
abbrev RealPoints := Discrete ℝ

/-- `ℝ ⊆ ℂ`. -/
def realToComplex : RealPoints ⥤ ComplexPoints := Discrete.functor fun x => ⟨(x : ℂ)⟩

def re : ComplexPoints ⥤ RealPoints := Discrete.functor fun z => ⟨z.re⟩
def im : ComplexPoints ⥤ RealPoints := Discrete.functor fun z => ⟨z.im⟩
def conj : ComplexPoints ⥤ ComplexPoints := Discrete.functor fun z => ⟨starRingEnd ℂ z⟩
def abs : ComplexPoints ⥤ RealPoints := Discrete.functor fun z => ⟨‖z‖⟩

/-- The Gaussian rationals within `ε` of `z`. -/
def approximationSet (z : ℂ) (ε : ℚ) : Set (ℚ × ℚ) :=
  {q | ‖z - ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)‖ ≤ ε}

def approximations : ComplexPoints ⥤ Discrete (ℚ → Set (ℚ × ℚ)) :=
  Discrete.functor fun z => ⟨approximationSet z⟩

/-- Functions between sets. -/
abbrev FunctionPoints := Discrete (Σ A B : Type u, A → B)

/-- `image`: a function's range, as a subset of its codomain. -/
def image : FunctionPoints.{u} ⥤ LeanCategories.Foundation.Subsets.{u} :=
  Discrete.functor fun F =>
    ⟨Arrow.mk (TypeCat.ofHom (Subtype.val : Set.range F.2.2 → F.2.1)),
      (mono_iff_injective _).2 Subtype.val_injective⟩

/-- Real functions. -/
abbrev RealFunctionPoints := Discrete (ℝ → ℝ)

/-- A real function is a function. -/
def realFunctionToFunction : RealFunctionPoints ⥤ FunctionPoints.{0} :=
  Discrete.functor fun f => ⟨⟨ℝ, ℝ, f⟩⟩

/-- The filter at an extended real: `atTop`, `atBot`, or the punctured neighbourhoods. -/
def approachFilter : EReal → Filter ℝ
  | ⊤ => atTop
  | ⊥ => atBot
  | (a : ℝ) => 𝓝[≠] a

/-- The limits of `f` at `a`, in the extended reals. -/
def limitSet (f : ℝ → ℝ) (a : EReal) : Set EReal :=
  {L | Tendsto (fun x => (f x : EReal)) (approachFilter a) (𝓝 L)}

def limits : RealFunctionPoints ⥤ Discrete (EReal → Set EReal) :=
  Discrete.functor fun f => ⟨limitSet f⟩

def integral : RealFunctionPoints ⥤ Discrete (ℝ → ℝ → ℝ) :=
  Discrete.functor fun f => ⟨fun a b => ∫ x in a..b, f x⟩

/-- The degree-`n` Taylor polynomial of `f` at `0`. -/
def taylorPolynomial (f : ℝ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (iteratedDeriv k f 0 / k.factorial) * X ^ k

def taylor : RealFunctionPoints ⥤ Discrete (ℕ → ℝ[X]) :=
  Discrete.functor fun f => ⟨taylorPolynomial f⟩

end

end LeanCategories.Analytic
