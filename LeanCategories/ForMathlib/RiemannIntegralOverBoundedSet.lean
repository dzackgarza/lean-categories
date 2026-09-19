/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

/-!
# Riemann integration over a bounded subset of Euclidean space

Lee, *Introduction to Smooth Manifolds*, second edition (2013), Appendix C, equation (C.11)
(`FC08-CC-U029`), extends a bounded function on a bounded set by zero. The function is called
integrable over the set when this extension is Riemann integrable on some containing closed
rectangle, and its integral is the value on such a rectangle.

`BoxIntegral.IntegrationParams.Riemann` is Mathlib's tagged-partition Riemann integral. Its
ambient domain is the closed box `Box.Icc I`; the half-open coercion of `Box` is used to make
partition cells disjoint and does not remove boundary values from the integrand. The final source
claim that integrability and the value are independent of the containing rectangle is a property
of these definitions and is not asserted here.
-/

@[expose] public section

open Set

namespace LeanCategories.ForMathlib

variable {n : ℕ}

/-- The extension by zero of a real-valued function on a subset of `ℝⁿ`, as in Lee's
equation (C.11). -/
noncomputable def riemannZeroExtension (D : Set (Fin n → ℝ)) (f : D → ℝ) :
    (Fin n → ℝ) → ℝ :=
  Function.extend Subtype.val f 0

/-- Riemann integrability of a bounded function over a bounded subset of `ℝⁿ`.

This is Lee's defining existence condition: the zero extension is Riemann integrable on some
closed rectangle containing the set.
-/
def IsRiemannIntegrableOver (D : Set (Fin n → ℝ)) (f : D → ℝ) : Prop :=
  Bornology.IsBounded D ∧ Bornology.IsBounded (range f) ∧
    ∃ I : BoxIntegral.Box (Fin n), D ⊆ BoxIntegral.Box.Icc I ∧
      BoxIntegral.Integrable I BoxIntegral.IntegrationParams.Riemann
        (riemannZeroExtension D f) BoxIntegral.BoxAdditiveMap.volume

/-- The Riemann integral of a bounded function over a bounded subset of `ℝⁿ`, obtained by
choosing the containing closed rectangle supplied by `IsRiemannIntegrableOver` and taking the
native box integral there. -/
noncomputable def riemannIntegralOver (D : Set (Fin n → ℝ)) (f : D → ℝ)
    (h : IsRiemannIntegrableOver D f) : ℝ :=
  BoxIntegral.integral h.2.2.choose BoxIntegral.IntegrationParams.Riemann
    (riemannZeroExtension D f) BoxIntegral.BoxAdditiveMap.volume

end LeanCategories.ForMathlib
