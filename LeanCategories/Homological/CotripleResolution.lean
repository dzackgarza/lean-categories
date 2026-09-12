/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monad.Basic

/-!
# Canonical simplicial data of a cotriple

Weibel, *An Introduction to Homological Algebra*, Construction 8.6.4, pp. 278--285
(FC05-C08-U061).

For a cotriple `T` and object `A`, Weibel sets `(T_* A)_n = T^{n+1} A`.  The `i`th face applies the
counit after `i` outer copies of `T`, and the `i`th degeneracy applies the comultiplication after
`i` outer copies of `T`.  This file records those construction formulas directly.  The assertion
that the formulas satisfy the simplicial identities and hence assemble into an augmented
simplicial object is result-level content of the construction theorem and belongs to Sweep IV.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Comonad

universe u v

variable {C : Type u} [Category.{v} C]

/-- The `n`-fold iterate `T^n(A)` of the endofunctor underlying a cotriple.

Source: Weibel, Construction 8.6.4 (FC05-C08-U061). -/
def iterObj (T : Comonad C) (A : C) : ℕ → C
  | 0 => A
  | n + 1 => T.obj (iterObj T A n)

/-- The functorial action of the `n`-fold iterate `T^n` on a morphism.

Source: Weibel, Construction 8.6.4 (FC05-C08-U061). -/
def iterMap (T : Comonad C) {A B : C} (f : A ⟶ B) : (n : ℕ) → iterObj T A n ⟶ iterObj T B n
  | 0 => f
  | n + 1 => T.map (iterMap T f n)

/-- The degree-`n` object of the canonical simplicial construction, namely `T^{n+1}(A)`.

Source: Weibel, Construction 8.6.4 (FC05-C08-U061). -/
abbrev simplicialDegree (T : Comonad C) (A : C) (n : ℕ) : C :=
  T.iterObj A (n + 1)

/-- The `i`th face `T^{n+1}(A) ⟶ T^n(A)` of the canonical cotriple construction.
Recursively, the zeroth face is the counit and each later face is obtained by applying `T` to the
corresponding face one degree lower; this is exactly `T^i ε T^{n-i}`.

Source: Weibel, Construction 8.6.4 (FC05-C08-U061). -/
def face (T : Comonad C) (A : C) : (n : ℕ) → Fin (n + 1) → (T.iterObj A (n + 1) ⟶ T.iterObj A n)
  | 0, _ => T.ε.app A
  | n + 1, i => Fin.cases (T.ε.app (T.iterObj A (n + 1)))
      (fun j => T.map (face T A n j)) i

/-- The `i`th degeneracy `T^{n+1}(A) ⟶ T^{n+2}(A)` of the canonical cotriple construction.
Recursively, the zeroth degeneracy is the comultiplication and each later degeneracy is obtained by
applying `T` to the corresponding degeneracy one degree lower; this is exactly `T^i δ T^{n-i}`.

Source: Weibel, Construction 8.6.4 (FC05-C08-U061). -/
def degeneracy (T : Comonad C) (A : C) :
    (n : ℕ) → Fin (n + 1) → (T.iterObj A (n + 1) ⟶ T.iterObj A (n + 2))
  | 0, _ => T.δ.app A
  | n + 1, i => Fin.cases (T.δ.app (T.iterObj A (n + 1)))
      (fun j => T.map (degeneracy T A n j)) i

/-- The augmentation `T(A) ⟶ A` of the canonical cotriple construction.

Source: Weibel, Construction 8.6.4 (FC05-C08-U061). -/
abbrev augmentation (T : Comonad C) (A : C) : T.iterObj A 1 ⟶ A :=
  T.ε.app A

end CategoryTheory.Comonad
