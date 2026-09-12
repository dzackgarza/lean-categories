/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CrossedModule

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

end FourTermCrossedExtension

end LeanCategories.Homological
