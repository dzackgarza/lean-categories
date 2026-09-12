/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.GroupFactorSet

/-!
# Difference between two sections of a group extension

Weibel, *An Introduction to Homological Algebra* (1994), Construction 6.6.8,
pp. 182--188 (FC05-C06-U072).

Two based sections of the same extension differ pointwise by a unique kernel
term.  This file records that normalized one-cochain and its defining equation.
The formula identifying the quotient of the two factor sets with its
coboundary is result-level content.
-/

@[expose] public section

namespace GroupExtension

universe uN uE uG

variable {N : Type uN} {E : Type uE} {G : Type uG}
  [Group N] [Group E] [Group G]

/-- The kernel-valued function comparing two based sections, chosen so that
`σ(g) = inl(c(g)) τ(g)`. -/
noncomputable def sectionDiffFun (S : GroupExtension N E G)
    (σ τ : S.BasedSection) (g : G) : N :=
  Classical.choose (σ.toSection.exists_eq_inl_mul τ.toSection g)

/-- Defining equation for the section-difference function. -/
theorem sectionDiffFun_spec (S : GroupExtension N E G)
    (σ τ : S.BasedSection) (g : G) :
    σ g = S.inl (S.sectionDiffFun σ τ g) * τ g :=
  Classical.choose_spec (σ.toSection.exists_eq_inl_mul τ.toSection g)

@[simp]
theorem sectionDiffFun_one (S : GroupExtension N E G)
    (σ τ : S.BasedSection) : S.sectionDiffFun σ τ 1 = 1 := by
  apply S.inl_injective
  have h := S.sectionDiffFun_spec σ τ 1
  simp only [BasedSection.apply_one, mul_one] at h
  simpa using h.symm

/-- A normalized multiplicative one-cochain on `G` with values in `N`. -/
structure NormalizedOneCochain where
  toFun : G → N
  map_one : toFun 1 = 1

instance : CoeFun (NormalizedOneCochain (N := N) (G := G)) (fun _ => G → N) :=
  ⟨NormalizedOneCochain.toFun⟩

/-- The normalized one-cochain measuring the change from `τ` to `σ`. -/
noncomputable def sectionDiff (S : GroupExtension N E G)
    (σ τ : S.BasedSection) : NormalizedOneCochain (N := N) (G := G) where
  toFun := S.sectionDiffFun σ τ
  map_one := S.sectionDiffFun_one σ τ

end GroupExtension
