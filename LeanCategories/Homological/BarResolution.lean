/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.Resolution

/-!
# Normalized and unnormalized bar terms

Weibel, *An Introduction to Homological Algebra*, §6.5, pp. 177–181
(FC05-C06-U048).

The source first specifies the free `ℤ[G]`-modules underlying the unnormalized and normalized bar
constructions.  The unnormalized degree-`n` basis consists of arbitrary symbols
`[g₁|...|gₙ]`; the normalized basis excludes the identity in every slot.  The differential is the
separate Definition 6.5.1 (U049), and exactness/free-resolution status is Theorem 6.5.3 (U052), so
neither is duplicated here.

Pinned Mathlib's `Rep.barComplex` uses the same unnormalized free term.  We state the term directly
through the universe-polymorphic `Rep.free` owner so the source construction is not restricted by
`Rep.barComplex`'s same-universe parameterization.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

universe u

variable (G : Type u) [Group G]

/-- Basis symbols `[g₁|...|gₙ]` for the unnormalized bar construction. -/
abbrev UnnormalizedBarBasis (n : ℕ) := Fin n → G

/-- Basis symbols `[g₁|...|gₙ]` for the normalized bar construction: every entry is nonidentity.
Source: Weibel, §6.5, pp. 177–178 (FC05-C06-U048). -/
abbrev NormalizedBarBasis (n : ℕ) := Fin n → {g : G // g ≠ 1}

/-- The degree-`n` free `ℤ[G]`-module of the unnormalized bar construction.  This is the
universe-polymorphic form of the term used by Mathlib's `Rep.barComplex`. -/
noncomputable abbrev unnormalizedBarTerm (n : ℕ) : Rep ℤ G :=
  Rep.free ℤ G (UnnormalizedBarBasis G n)

/-- The degree-`n` free `ℤ[G]`-module of the normalized bar construction. -/
noncomputable abbrev normalizedBarTerm (n : ℕ) : Rep ℤ G :=
  Rep.free ℤ G (NormalizedBarBasis G n)

end LeanCategories.Homological
