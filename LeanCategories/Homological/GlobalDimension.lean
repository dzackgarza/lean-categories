/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Global and weak dimensions of rings

Weibel, *An Introduction to Homological Algebra*, §4.1 (pp. 90–91).

The **(right) global dimension** of a ring `R` is defined (Def. 4.1.1) as

  r.gl.dim(R) = sup { pd(A) : A ∈ mod-R }

The **(right) injective global dimension** is (Thm. 4.1.2)

  sup { id(B) : B ∈ mod-R }

These are equal by the Global Dimension Theorem (4.1.2).

The **(right) weak dimension** (Tor-dimension, Thm. 4.1.3) is

  r.wd(R) = sup { fd(A) : A ∈ mod-R }

We define the first two; weak dimension is left for future work since Mathlib
does not yet have a `flatDimension` analogue.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

/-- The (right) global dimension of a ring `R` (Weibel, Def. 4.1.1).
    This is `sup { pd(M) | M is a right R-module }`.

    Since `projectiveDimension` takes values in the universe-free type
    `WithBot ℕ∞`, the supremum value is independent of the carrier universe.
    We fix both carrier and ring universes to be the same for convenience. -/
noncomputable def globalDimension.{u} (R : Type u) [Ring R] : WithBot ℕ∞ :=
  sSup (Set.range fun (M : ModuleCat.{u, u} R) => projectiveDimension M)

/-- The (right) injective global dimension of a ring `R` (Weibel, Thm. 4.1.2(1)).
    This is `sup { id(M) | M is a right R-module }`. -/
noncomputable def injectiveGlobalDimension.{u} (R : Type u) [Ring R] : WithBot ℕ∞ :=
  sSup (Set.range fun (M : ModuleCat.{u, u} R) => injectiveDimension M)

namespace globalDimension

set_option synthInstance.maxHeartbeats 40000 in
-- higher heartbeat limit needed for Module.Projective.of_basis synthesis

/-- A division ring has global dimension zero (Weibel, Example 4.1.4).
    Every module over a division ring is free, hence projective,
    so pd = 0 for all modules. -/
theorem of_divisionRing {R : Type*} [DivisionRing R] :
    globalDimension R = 0 := by
  rw [globalDimension]
  apply le_antisymm
  · -- Upper bound: every M has pd ≤ 0
    apply sSup_le
    rintro d ⟨M, rfl⟩
    -- Fix beta-redex: (fun M ↦ projectiveDimension M) M → projectiveDimension M
    change projectiveDimension M ≤ 0
    -- M is projective over a division ring
    haveI : Module.Projective R (M : Type _) :=
      Module.Projective.of_basis (Module.Basis.ofVectorSpace R M)
    have hP : Projective M :=
      ModuleCat.projective_of_categoryTheory_projective M
    -- pd(M) ≤ 0 since M is projective
    exact projectiveDimension_le_iff M 0 |>.mpr
      (Iff.mp (projective_iff_hasProjectiveDimensionLE_zero M) hP)
  · -- Lower bound: 0 ≤ sSup (need an element with pd = 0)
    apply le_sSup
    refine ⟨ModuleCat.of R R, ?_⟩
    change projectiveDimension (ModuleCat.of R R) = 0
    rw [projectiveDimension_eq_zero_iff]
    constructor
    · -- R is projective as a module over itself
      haveI : Module.Projective R R :=
        Module.Projective.of_basis (Module.Basis.singleton Unit R)
      exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of R R)
    · -- R as a module is not the zero object (since 1 ≠ 0)
      intro h
      have heq := h.eq_of_src (f := 𝟙 (ModuleCat.of R R)) (g := 0)
      have h0 := ModuleCat.Hom.ext_iff.mp heq
      have h1 := LinearMap.ext_iff.mp h0 1
      simp at h1
      exact absurd h1 one_ne_zero

end globalDimension

end LeanCategories.Homological
