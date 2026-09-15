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
term.  This file constructs that normalized one-cochain, proves that the
quotient of their factor sets is its multiplicative `2`-coboundary, and deduces
that the corresponding class in `H²` is independent of the based section.
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
theorem inl_sectionDiffFun (S : GroupExtension N E G)
    (σ τ : S.BasedSection) (g : G) :
    S.inl (S.sectionDiffFun σ τ g) = σ g * (τ g)⁻¹ := by
  have h := S.sectionDiffFun_spec σ τ g
  rw [h]
  group

@[simp]
theorem sectionDiffFun_one (S : GroupExtension N E G)
    (σ τ : S.BasedSection) : S.sectionDiffFun σ τ 1 = 1 := by
  apply S.inl_injective
  have h := S.sectionDiffFun_spec σ τ 1
  simp only [BasedSection.apply_one, mul_one] at h
  rw [map_one]
  exact h.symm

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

@[simp]
theorem inl_sectionDiff (S : GroupExtension N E G)
    (σ τ : S.BasedSection) (g : G) :
    S.inl (S.sectionDiff σ τ g) = σ g * (τ g)⁻¹ := by
  change S.inl (S.sectionDiffFun σ τ g) = _
  exact S.inl_sectionDiffFun σ τ g

section Coboundary

variable {M : Type uN} [CommGroup M] [MulDistribMulAction G M]
  {T : GroupExtension M E G}

/-- Changing a based section changes its factor set by the multiplicative
`2`-coboundary of the normalized section-difference cochain. -/
theorem isMulCoboundary₂_div (σ τ : T.BasedSection)
    (hact : T.InducesAction) :
    groupCohomology.IsMulCoboundary₂ fun p : G × G =>
      T.factorSetFun σ p.1 p.2 / T.factorSetFun τ p.1 p.2 := by
  refine ⟨fun g => T.sectionDiff σ τ g, fun g h => ?_⟩
  have e₁ : (σ g : E) * σ h =
      T.inl (T.factorSetFun σ g h * T.sectionDiff σ τ (g * h)) * τ (g * h) := by
    rw [map_mul, T.inl_factorSetFun, T.inl_sectionDiff]
    group
  have e₂ : (σ g : E) * σ h =
      T.inl (g • T.sectionDiff σ τ h * T.sectionDiff σ τ g * T.factorSetFun τ g h) *
        τ (g * h) := by
    rw [map_mul, map_mul, T.inl_smul σ hact,
      T.inl_sectionDiff, T.inl_sectionDiff, T.inl_factorSetFun]
    group
  have key := T.inl_injective (mul_right_cancel (e₁.symm.trans e₂))
  rw [div_mul_eq_mul_div, div_eq_div_iff_mul_eq_mul, ← key]

end Coboundary

section H2

open groupCohomology

variable {M₀ G₀ : Type} [CommGroup M₀] [Group G₀] [MulDistribMulAction G₀ M₀]
  {E₀ : Type uE} [Group E₀] {T₀ : GroupExtension M₀ E₀ G₀}

/-- The `H²` class represented by the factor set of an extension is independent
of the chosen based section. -/
theorem cohomologyClass_factorSet_eq (σ τ : T₀.BasedSection)
    (hact : T₀.InducesAction) :
    T₀.factorSetCohomologyClass σ hact = T₀.factorSetCohomologyClass τ hact := by
  rw [factorSetCohomologyClass, factorSetCohomologyClass, H2π_eq_iff]
  have hfun :
      ⇑(T₀.factorSetCocycle σ hact) - ⇑(T₀.factorSetCocycle τ hact) =
        fun p : G₀ × G₀ => Additive.ofMul
          (T₀.factorSetFun σ p.1 p.2 / T₀.factorSetFun τ p.1 p.2) := by
    funext p
    exact (ofMul_div _ _).symm
  rw [hfun]
  change (Additive.ofMul ∘ fun p : G₀ × G₀ =>
    T₀.factorSetFun σ p.1 p.2 / T₀.factorSetFun τ p.1 p.2) ∈
      coboundaries₂ (Rep.ofMulDistribMulAction G₀ M₀)
  exact (coboundariesOfIsMulCoboundary₂ (T₀.isMulCoboundary₂_div σ τ hact)).2

end H2

end GroupExtension
