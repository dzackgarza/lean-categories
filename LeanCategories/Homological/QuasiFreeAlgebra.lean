/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildExtensions

/-!
# Quasi-free associative algebras

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.3.2,
pp. 311--318 (FC05-C09-U031).

For an associative `k`-algebra `R`, quasi-freeness means that every `k`-algebra
map from `R` into the quotient of a square-zero extension lifts to the middle
algebra.  This is the noncommutative lifting property used by Weibel.

The assertion that free associative algebras are quasi-free is theorem-layer
content and is deliberately not included here.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v w x z

/-- Weibel's quasi-free predicate for an arbitrary associative `k`-algebra.

For every target algebra `T`, every `T`-bimodule `M`, every square-zero
extension `E → T` by `M`, and every algebra map `R → T`, a lift `R → E`
exists over `T`.

Source: Weibel, Definition 9.3.2 (FC05-C09-U031). -/
def IsQuasiFreeAlgebra (k : Type u) [CommRing k]
    (R : Type v) [Ring R] [Algebra k R] : Prop :=
  ∀ (T : Type w) [Ring T] [Algebra k T]
    (M : Type x) [AddCommGroup M] [Module k M]
    [Module T M] [Module Tᵐᵒᵖ M],
    ∀ (S : SquareZeroExtension.{u, w, x, z} k T M) (f : R →ₐ[k] T),
      ∃ g : R →ₐ[k] S.E, S.projection.comp g = f

end LeanCategories.Homological
