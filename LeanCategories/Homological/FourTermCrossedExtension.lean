/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CrossedModule
public import Mathlib.Tactic.Group

/-!
# Four-term crossed extensions and their three-cochain data

Weibel, *An Introduction to Homological Algebra* (1994), Construction 6.6.12,
§6.6, pp. 182--188 (FC05-C06-U076).

The construction starts from an exact four-term sequence
`1 → A → N → E → G → 1` whose left kernel is central, together with the
crossed-module action of `E` on `N`.  A normalized section `G → E`, normalized
lifts of its multiplicative defect to `N`, and a lift of the resulting
associativity defect to `A` determine the normalized three-cochain used in the
source.  The theorem that this three-cochain is a cocycle, and the independence
of its cohomology class from the choices, belong to Sweep IV.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u

/-- A crossed-module presentation of an exact four-term extension
`1 → A → N → E → G → 1` with central left kernel.

This is the structural input of Weibel Construction 6.6.12. -/
structure FourTermCrossedExtension
    (A N E G : Type u) [Group A] [Group N] [Group E] [Group G]
    extends CrossedModule N E where
  /-- Inclusion of the coefficient group into the crossed-module kernel. -/
  inl : A →* N
  /-- Projection onto the cokernel group. -/
  projection : E →* G
  /-- Exactness at `A`. -/
  inl_injective : Function.Injective inl
  /-- Exactness at `N`. -/
  range_inl_eq_ker_boundary : inl.range = toCrossedModule.boundary.ker
  /-- Exactness at `E`. -/
  range_boundary_eq_ker_projection : toCrossedModule.boundary.range = projection.ker
  /-- Exactness at `G`. -/
  projection_surjective : Function.Surjective projection
  /-- The image of `A` is central in `N`. -/
  central_inl : inl.range ≤ Subgroup.center N

namespace FourTermCrossedExtension

variable {A N E G : Type u} [Group A] [Group N] [Group E] [Group G]

@[simp]
lemma act_one (X : FourTermCrossedExtension A N E G) (n : N) : X.act 1 n = n := by
  simp [CrossedModule.act]

@[simp]
lemma act_one_mem (X : FourTermCrossedExtension A N E G) (e : E) : X.act e 1 = 1 := by
  simp [CrossedModule.act]

/-- A normalized multiplicative three-cochain `G³ → A`.

No cocycle equation is part of this definition. -/
structure NormalizedThreeCochain where
  /-- Underlying three-cochain. -/
  toFun : G → G → G → A
  /-- Normalization in the first argument. -/
  map_one_first : ∀ h k, toFun 1 h k = 1
  /-- Normalization in the second argument. -/
  map_one_second : ∀ g k, toFun g 1 k = 1
  /-- Normalization in the third argument. -/
  map_one_third : ∀ g h, toFun g h 1 = 1

instance : CoeFun (NormalizedThreeCochain (A := A) (G := G))
    (fun _ => G → G → G → A) :=
  ⟨NormalizedThreeCochain.toFun⟩

/-- A normalized set-theoretic section of the four-term projection. -/
noncomputable def canonicalSection (X : FourTermCrossedExtension A N E G) (g : G) : E :=
  by
    classical
    exact if h : g = 1 then 1 else Classical.choose (X.projection_surjective g)

@[simp]
lemma canonicalSection_one (X : FourTermCrossedExtension A N E G) :
    X.canonicalSection 1 = 1 := by
  simp [canonicalSection]

@[simp]
lemma projection_canonicalSection (X : FourTermCrossedExtension A N E G) (g : G) :
    X.projection (X.canonicalSection g) = g := by
  classical
  by_cases h : g = 1
  · subst g
    simp
  · simp only [canonicalSection, dif_neg h]
    exact Classical.choose_spec (X.projection_surjective g)

/-- The multiplicative defect of the normalized section. -/
noncomputable def sectionDefect (X : FourTermCrossedExtension A N E G) (g h : G) : E :=
  X.canonicalSection g * X.canonicalSection h * (X.canonicalSection (g * h))⁻¹

@[simp]
lemma projection_sectionDefect (X : FourTermCrossedExtension A N E G) (g h : G) :
    X.projection (X.sectionDefect g h) = 1 := by
  simp [sectionDefect]

lemma sectionDefect_mem_boundary_range
    (X : FourTermCrossedExtension A N E G) (g h : G) :
    X.sectionDefect g h ∈ X.boundary.range := by
  rw [X.range_boundary_eq_ker_projection]
  exact MonoidHom.mem_ker.mpr (X.projection_sectionDefect g h)

/-- An arbitrary lift in `N` of the section defect. -/
noncomputable def rawFactorLift (X : FourTermCrossedExtension A N E G) (g h : G) : N :=
  Classical.choose (MonoidHom.mem_range.mp (X.sectionDefect_mem_boundary_range g h))

@[simp]
lemma boundary_rawFactorLift (X : FourTermCrossedExtension A N E G) (g h : G) :
    X.boundary (X.rawFactorLift g h) = X.sectionDefect g h :=
  Classical.choose_spec (MonoidHom.mem_range.mp (X.sectionDefect_mem_boundary_range g h))

/-- The normalized lift `u(g,h)` of the multiplication defect. -/
noncomputable def canonicalFactorLift
    (X : FourTermCrossedExtension A N E G) (g h : G) : N :=
  by
    classical
    exact if hg : g = 1 then 1 else if hh : h = 1 then 1 else X.rawFactorLift g h

@[simp]
lemma canonicalFactorLift_one_left
    (X : FourTermCrossedExtension A N E G) (g : G) :
    X.canonicalFactorLift 1 g = 1 := by
  simp [canonicalFactorLift]

@[simp]
lemma canonicalFactorLift_one_right
    (X : FourTermCrossedExtension A N E G) (g : G) :
    X.canonicalFactorLift g 1 = 1 := by
  classical
  by_cases hg : g = 1 <;> simp [canonicalFactorLift, hg]

@[simp]
lemma boundary_canonicalFactorLift
    (X : FourTermCrossedExtension A N E G) (g h : G) :
    X.boundary (X.canonicalFactorLift g h) = X.sectionDefect g h := by
  classical
  by_cases hg : g = 1
  · subst g
    simp [sectionDefect]
  · by_cases hh : h = 1
    · subst h
      simp [sectionDefect]
    · simp [canonicalFactorLift, hg, hh]

/-- The associativity defect of the lifted factor set. -/
noncomputable def associativityDefect
    (X : FourTermCrossedExtension A N E G) (g h k : G) : N :=
  X.act (X.canonicalSection g) (X.canonicalFactorLift h k) *
    X.canonicalFactorLift g (h * k) *
    (X.canonicalFactorLift (g * h) k)⁻¹ *
    (X.canonicalFactorLift g h)⁻¹

/-- The associativity defect has trivial boundary, hence lies in the image of
`A`. -/
@[simp]
lemma boundary_associativityDefect
    (X : FourTermCrossedExtension A N E G) (g h k : G) :
    X.boundary (X.associativityDefect g h k) = 1 := by
  simp only [associativityDefect, map_mul, map_inv, X.boundary_act,
    X.boundary_canonicalFactorLift, sectionDefect]
  group

lemma associativityDefect_mem_inl_range
    (X : FourTermCrossedExtension A N E G) (g h k : G) :
    X.associativityDefect g h k ∈ X.inl.range := by
  rw [X.range_inl_eq_ker_boundary]
  exact MonoidHom.mem_ker.mpr (X.boundary_associativityDefect g h k)

/-- The `A`-valued associativity defect. -/
noncomputable def threeCochainFun
    (X : FourTermCrossedExtension A N E G) (g h k : G) : A :=
  Classical.choose (MonoidHom.mem_range.mp (X.associativityDefect_mem_inl_range g h k))

@[simp]
lemma inl_threeCochainFun
    (X : FourTermCrossedExtension A N E G) (g h k : G) :
    X.inl (X.threeCochainFun g h k) = X.associativityDefect g h k :=
  Classical.choose_spec (MonoidHom.mem_range.mp (X.associativityDefect_mem_inl_range g h k))

@[simp]
lemma threeCochainFun_one_first
    (X : FourTermCrossedExtension A N E G) (h k : G) :
    X.threeCochainFun 1 h k = 1 := by
  apply X.inl_injective
  rw [X.inl_threeCochainFun]
  simp [associativityDefect]

@[simp]
lemma threeCochainFun_one_second
    (X : FourTermCrossedExtension A N E G) (g k : G) :
    X.threeCochainFun g 1 k = 1 := by
  apply X.inl_injective
  rw [X.inl_threeCochainFun]
  simp [associativityDefect]

@[simp]
lemma threeCochainFun_one_third
    (X : FourTermCrossedExtension A N E G) (g h : G) :
    X.threeCochainFun g h 1 = 1 := by
  apply X.inl_injective
  rw [X.inl_threeCochainFun]
  simp [associativityDefect]

/-- The normalized three-cochain produced by Weibel's construction. -/
noncomputable def canonicalThreeCochain
    (X : FourTermCrossedExtension A N E G) : NormalizedThreeCochain (A := A) (G := G) where
  toFun := X.threeCochainFun
  map_one_first := X.threeCochainFun_one_first
  map_one_second := X.threeCochainFun_one_second
  map_one_third := X.threeCochainFun_one_third

/-- The choices entering Weibel's four-term-extension construction.

The final field is the defining equation for the `A`-valued associativity
defect.  Its image in `N` is
`(s(g) · u(h,k)) u(g,hk) u(gh,k)⁻¹ u(g,h)⁻¹`.
The assertion that this normalized three-cochain is a cocycle is deliberately
not included here. -/
structure Choices (X : FourTermCrossedExtension A N E G) where
  /-- Normalized set-theoretic section `s : G → E`. -/
  sectionMap : G → E
  /-- The section is based. -/
  section_one : sectionMap 1 = 1
  /-- `s` is a section of the projection. -/
  projection_section : Function.RightInverse sectionMap X.projection
  /-- A normalized lift `u(g,h)` of the multiplicative defect of `s`. -/
  factorLift : G → G → N
  /-- Left normalization of `u`. -/
  factorLift_one_left : ∀ g, factorLift 1 g = 1
  /-- Right normalization of `u`. -/
  factorLift_one_right : ∀ g, factorLift g 1 = 1
  /-- `u(g,h)` lifts `s(g)s(h)s(gh)⁻¹`. -/
  boundary_factorLift : ∀ g h,
    X.boundary (factorLift g h) = sectionMap g * sectionMap h * (sectionMap (g * h))⁻¹
  /-- The normalized `A`-valued associativity defect. -/
  threeCochain : NormalizedThreeCochain (A := A) (G := G)
  /-- Defining equation for the associativity defect. -/
  inl_threeCochain : ∀ g h k,
    X.inl (threeCochain g h k) =
      X.act (sectionMap g) (factorLift h k) * factorLift g (h * k) *
      (factorLift (g * h) k)⁻¹ * (factorLift g h)⁻¹

/-- The source choices exist canonically (noncomputably) from exactness. -/
noncomputable def canonicalChoices (X : FourTermCrossedExtension A N E G) : X.Choices where
  sectionMap := X.canonicalSection
  section_one := X.canonicalSection_one
  projection_section := X.projection_canonicalSection
  factorLift := X.canonicalFactorLift
  factorLift_one_left := X.canonicalFactorLift_one_left
  factorLift_one_right := X.canonicalFactorLift_one_right
  boundary_factorLift := X.boundary_canonicalFactorLift
  threeCochain := X.canonicalThreeCochain
  inl_threeCochain := X.inl_threeCochainFun

end FourTermCrossedExtension

end LeanCategories.Homological
