/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Factor sets of group extensions

Weibel, *An Introduction to Homological Algebra* (1994), Definition 6.6.4,
§6.6, pp. 182--188 (FC05-C06-U068).

For an extension `1 → N → E → G → 1` and a based set-theoretic section
`σ : G → E`, the factor set is the unique kernel element `[g,h]` satisfying

`σ(g) σ(h) = inl([g,h]) σ(gh)`.

The factor-set cocycle law and its degree-two cohomology class are included
because Construction 6.6.8 compares the classes arising from different based
sections.  The actual section-change coboundary is developed in
`GroupSectionDifference`.
-/

@[expose] public section

namespace GroupExtension

open groupCohomology

universe uN uE uG

variable {N : Type uN} {E : Type uE} {G : Type uG}
  [Group N] [Group E] [Group G]

/-- A set-theoretic section of a group extension normalized by `σ(1)=1`. -/
structure BasedSection (S : GroupExtension N E G) extends S.Section where
  map_one : toFun 1 = 1

namespace BasedSection

variable {S : GroupExtension N E G}

instance : CoeFun S.BasedSection (fun _ => G → E) :=
  ⟨fun σ => σ.toFun⟩

@[simp]
theorem rightHom_apply (σ : S.BasedSection) (g : G) :
    S.rightHom (σ g) = g :=
  σ.toSection.rightInverse_rightHom g

@[simp]
theorem apply_one (σ : S.BasedSection) : σ 1 = 1 :=
  σ.map_one

end BasedSection

/-- The extension conjugates its kernel by the prescribed `G`-action. -/
def InducesAction (S : GroupExtension N E G) [MulDistribMulAction G N] : Prop :=
  ∀ (e : E) (n : N), S.conjAct e n = S.rightHom e • n

/-- If an extension induces the prescribed action, inclusion of the kernel
intertwines that action with conjugation by any based section. -/
theorem inl_smul (S : GroupExtension N E G) [MulDistribMulAction G N]
    (σ : S.BasedSection) (hact : S.InducesAction) (g : G) (n : N) :
    S.inl (g • n) = σ g * S.inl n * (σ g)⁻¹ := by
  have h := hact (σ g) n
  rw [BasedSection.rightHom_apply] at h
  rw [← h, GroupExtension.inl_conjAct_comm]

/-- The kernel element measuring the failure of a based section to preserve
multiplication. -/
noncomputable def factorSetFun (S : GroupExtension N E G) (σ : S.BasedSection)
    (g h : G) : N :=
  Classical.choose <|
    (MonoidHom.mem_range.mp (σ.toSection.mul_mul_mul_inv_mem_range_inl g h))

@[simp]
theorem inl_factorSetFun (S : GroupExtension N E G) (σ : S.BasedSection)
    (g h : G) :
    S.inl (S.factorSetFun σ g h) = σ g * σ h * (σ (g * h))⁻¹ :=
  Classical.choose_spec <|
    (MonoidHom.mem_range.mp (σ.toSection.mul_mul_mul_inv_mem_range_inl g h))

/-- Weibel's defining factor-set equation
`σ(g)σ(h) = [g,h]σ(gh)`. -/
theorem factorSetFun_spec (S : GroupExtension N E G) (σ : S.BasedSection)
    (g h : G) :
    σ g * σ h = S.inl (S.factorSetFun σ g h) * σ (g * h) := by
  rw [S.inl_factorSetFun σ g h]
  group

@[simp]
theorem factorSetFun_one_left (S : GroupExtension N E G) (σ : S.BasedSection)
    (g : G) : S.factorSetFun σ 1 g = 1 := by
  apply S.inl_injective
  rw [S.inl_factorSetFun, σ.apply_one]
  simp

@[simp]
theorem factorSetFun_one_right (S : GroupExtension N E G) (σ : S.BasedSection)
    (g : G) : S.factorSetFun σ g 1 = 1 := by
  apply S.inl_injective
  rw [S.inl_factorSetFun, σ.apply_one]
  simp

/-- A normalized factor set arising from a chosen based section. -/
structure FactorSet (S : GroupExtension N E G) where
  toFun : G → G → N
  map_one_left : ∀ g, toFun 1 g = 1
  map_one_right : ∀ g, toFun g 1 = 1

/-- The normalized factor set associated to a based section. -/
noncomputable def factorSet (S : GroupExtension N E G) (σ : S.BasedSection) :
    S.FactorSet where
  toFun := S.factorSetFun σ
  map_one_left := S.factorSetFun_one_left σ
  map_one_right := S.factorSetFun_one_right σ

section Cocycle

variable {M : Type uN} [CommGroup M] [MulDistribMulAction G M]
  {T : GroupExtension M E G}

/-- The factor set of a based section is a multiplicative `2`-cocycle when the
extension induces the prescribed action on its abelian kernel. -/
theorem isMulCocycle₂_factorSetFun (σ : T.BasedSection)
    (hact : T.InducesAction) :
    IsMulCocycle₂ (fun p : G × G => T.factorSetFun σ p.1 p.2) := by
  intro g₁ g₂ g₃
  refine T.inl_injective ?_
  rw [mul_comm (T.factorSetFun σ (g₁ * g₂) g₃), map_mul, map_mul,
    T.inl_smul σ hact]
  simp only [T.inl_factorSetFun]
  rw [mul_assoc g₁ g₂ g₃]
  group

end Cocycle

section H2

-- Mathlib's current ordinary group-cohomology API fixes the group and
-- coefficient module in the universe of the coefficient ring `ℤ`.
variable {M₀ G₀ : Type} [CommGroup M₀] [Group G₀] [MulDistribMulAction G₀ M₀]
  {E₀ : Type uE} [Group E₀] {T₀ : GroupExtension M₀ E₀ G₀}

/-- The factor set of a based section, regarded as a `2`-cocycle in Mathlib's
inhomogeneous group-cohomology complex. -/
noncomputable def factorSetCocycle (σ : T₀.BasedSection) (hact : T₀.InducesAction) :
    cocycles₂ (Rep.ofMulDistribMulAction G₀ M₀) :=
  cocyclesOfIsMulCocycle₂ (isMulCocycle₂_factorSetFun σ hact)

/-- The degree-two cohomology class represented by the factor set of a based
section. -/
noncomputable def factorSetCohomologyClass (σ : T₀.BasedSection)
    (hact : T₀.InducesAction) : H2 (Rep.ofMulDistribMulAction G₀ M₀) :=
  H2π (Rep.ofMulDistribMulAction G₀ M₀) (factorSetCocycle σ hact)

end H2

end GroupExtension
