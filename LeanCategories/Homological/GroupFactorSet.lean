/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Factor sets of group extensions

Weibel, *An Introduction to Homological Algebra* (1994), Definition 6.6.4,
§6.6, pp. 182--188 (FC05-C06-U068).

For an extension `1 → N → E → G → 1` and a based set-theoretic section
`σ : G → E`, the factor set is the unique kernel element `[g,h]` satisfying

`σ(g) σ(h) = inl([g,h]) σ(gh)`.

The cocycle law and the comparison of different sections are theorem-layer
statements and are intentionally not developed here.
-/

@[expose] public section

namespace GroupExtension

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

end GroupExtension
