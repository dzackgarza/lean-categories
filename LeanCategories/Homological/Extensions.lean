/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Extensions of Modules and the Baer Sum

Weibel, *An Introduction to Homological Algebra*, §3.4 (pp. 76–80).

An **extension of `B` by `A`** (Def. 3.4.1) is a short exact sequence
of `R`-modules

  0 → A → E → B → 0.

Two extensions are **equivalent** if there is a morphism of short
complexes that is the identity on `A` and `B`. The **Baer sum** (Def.
3.4.4) makes the equivalence classes into an abelian group
`Ext¹(B, A)`, naturally isomorphic to the derived-functor Ext group.

This file provides:
* `Extension A B` — the type of extensions of `B` by `A`.
* `Extension.Equiv` — equivalence of extensions.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

/-- An **extension of `B` by `A`** (Weibel, Def. 3.4.1) is a short exact
    sequence `0 → A → E → B → 0` in the category of `R`-modules.

    We package this as a short complex that is short exact, together with
    the proof that its left and right terms are `A` and `B`. -/
structure Extension.{u} {R : Type u} [Ring R] (A B : ModuleCat.{u, u} R) where
  /-- The middle term of the extension. -/
  E : ModuleCat.{u, u} R
  /-- The underlying short complex. -/
  seq : ShortComplex (ModuleCat.{u, u} R)
  /-- The sequence is short exact. -/
  exact : seq.ShortExact
  /-- The left term is `A`. -/
  left_eq : seq.X₁ = A
  /-- The right term is `B`. -/
  right_eq : seq.X₃ = B

namespace Extension

/-- Two extensions `0 → A → E₁ → B → 0` and `0 → A → E₂ → B → 0`
    are **equivalent** (Weibel, Def. 3.4.1) if there exists a morphism of
    short complexes `τ : seq₁ → seq₂` with `τ.τ₁ = 𝟙 A` and
    `τ.τ₃ = 𝟙 B`. By the five lemma, `τ.τ₂` is then an isomorphism. -/
structure Equiv.{u} {R : Type u} [Ring R] {A B : ModuleCat.{u, u} R}
    (e₁ e₂ : Extension A B) where
  /-- The underlying morphism of short complexes. -/
  τ : e₁.seq ⟶ e₂.seq
  /-- The left component is the identity on `A` (transported through the
      endpoint equalities). -/
  τ₁_eq : τ.τ₁ =
    eqToHom e₁.left_eq ≫ eqToHom e₂.left_eq.symm
  /-- The right component is the identity on `B` (transported through the
      endpoint equalities). -/
  τ₃_eq : τ.τ₃ =
    eqToHom e₁.right_eq ≫ eqToHom e₂.right_eq.symm

end Extension

end LeanCategories.Homological
