/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Syzygies of a projective resolution

Weibel, *An Introduction to Homological Algebra* (1994), §2.4,
Exercise 2.4.3, pp. 43--48, FC05-C02-U045.

For an exact partial projective resolution
`0 ⟶ Mₘ ⟶ Pₘ ⟶ Pₘ₋₁ ⟶ ⋯ ⟶ P₀ ⟶ A ⟶ 0`, Weibel calls
`Mₘ` the `m`-th syzygy of `A`.  In a bundled projective resolution this
is the kernel of the augmentation in degree zero and the kernel of the
chain differential in successor degrees.

Mathlib's `Projective.syzygies f` has a different role: it is a chosen
projective object over `kernel f`, used to construct the next resolution
term.  The definitions below name the kernel object itself.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ProjectiveResolution

/-- The `m`th syzygy of `Z` determined by the projective resolution `P` in Weibel's
convention: the kernel at the `m`th projective term, with degree zero using the augmentation. -/
noncomputable def syzygy {Z : C} (P : CategoryTheory.ProjectiveResolution Z) : ℕ → C
  | 0 => kernel (P.π.f 0)
  | n + 1 => kernel (P.complex.d (n + 1) n)

/-- The canonical inclusion of the `m`th syzygy into the `m`th projective term. -/
noncomputable def syzygyι {Z : C} (P : CategoryTheory.ProjectiveResolution Z) :
    ∀ m : ℕ, syzygy P m ⟶ P.complex.X m
  | 0 => kernel.ι (P.π.f 0)
  | n + 1 => kernel.ι (P.complex.d (n + 1) n)

@[simp]
theorem syzygy_zero {Z : C} (P : CategoryTheory.ProjectiveResolution Z) :
    syzygy P 0 = kernel (P.π.f 0) := rfl

@[simp]
theorem syzygy_succ {Z : C} (P : CategoryTheory.ProjectiveResolution Z) (n : ℕ) :
    syzygy P (n + 1) = kernel (P.complex.d (n + 1) n) := rfl

@[reassoc (attr := simp)]
theorem syzygyι_zero_comp {Z : C} (P : CategoryTheory.ProjectiveResolution Z) :
    syzygyι P 0 ≫ P.π.f 0 = 0 :=
  kernel.condition _

@[reassoc (attr := simp)]
theorem syzygyι_succ_comp {Z : C} (P : CategoryTheory.ProjectiveResolution Z) (n : ℕ) :
    syzygyι P (n + 1) ≫ P.complex.d (n + 1) n = 0 :=
  kernel.condition _

end ProjectiveResolution

end LeanCategories.Homological
