/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildEnveloping

/-!
# Hochschild derivations and principal derivations

Weibel, *An Introduction to Homological Algebra* (1994), §9.2, pp. 306--310
(FC05-C09-U012).

Unlike Mathlib's commutative `Derivation`, these definitions retain Weibel's
arbitrary associative `k`-algebra and bimodule target.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v w

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module R M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]
  [SMulCommClass k R M] [SMulCommClass k Rᵐᵒᵖ M]

/-- The `k`-submodule of linear maps satisfying the bimodule Leibniz rule
`d(rs)=r d(s)+d(r)s`. -/
def hochschildDerivations : Submodule k (R →ₗ[k] M) where
  carrier := {d | ∀ r s : R,
    d (r * s) = r • d s + (MulOpposite.op s : Rᵐᵒᵖ) • d r}
  zero_mem' r s := by simp
  add_mem' {d e} hd he r s := by
    simp only [LinearMap.add_apply, hd r s, he r s, smul_add]
    abel_nf
  smul_mem' a d hd r s := by
    change a • d (r * s) = r • (a • d s) +
      (MulOpposite.op s : Rᵐᵒᵖ) • (a • d r)
    rw [hd r s]
    simp only [smul_add]
    rw [smul_comm a r, smul_comm a (MulOpposite.op s : Rᵐᵒᵖ)]

/-- Weibel's module `Der_k(R,M)` of bimodule-valued derivations. -/
abbrev HochschildDerivation := hochschildDerivations k R M

/-- The principal derivation associated to `m`, `r ↦ r m - m r`. -/
def principalDerivationLinearMap (m : M) : R →ₗ[k] M where
  toFun r := r • m - (MulOpposite.op r : Rᵐᵒᵖ) • m
  map_add' r s := by simp [add_smul, sub_add_sub_comm]
  map_smul' a r := by
    simp only [smul_sub]
    congr 1
    · exact smul_assoc a r m
    · change (a • (MulOpposite.op r : Rᵐᵒᵖ)) • m =
        a • ((MulOpposite.op r : Rᵐᵒᵖ) • m)
      exact smul_assoc a (MulOpposite.op r : Rᵐᵒᵖ) m

theorem principalDerivation_leibniz (m : M) (r s : R) :
    principalDerivationLinearMap k R M m (r * s) =
      r • principalDerivationLinearMap k R M m s +
        (MulOpposite.op s : Rᵐᵒᵖ) • principalDerivationLinearMap k R M m r := by
  simp only [principalDerivationLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [mul_smul, MulOpposite.op_mul, mul_smul]
  simp only [smul_sub]
  rw [smul_comm r (MulOpposite.op s : Rᵐᵒᵖ) m]
  abel

/-- The `k`-linear map sending `m` to its principal derivation. -/
noncomputable def principalDerivationMap : M →ₗ[k] HochschildDerivation k R M where
  toFun m := ⟨principalDerivationLinearMap k R M m, by
    change ∀ r s : R, principalDerivationLinearMap k R M m (r * s) =
      r • principalDerivationLinearMap k R M m s +
        (MulOpposite.op s : Rᵐᵒᵖ) • principalDerivationLinearMap k R M m r
    exact principalDerivation_leibniz k R M m⟩
  map_add' m n := by
    apply Subtype.ext
    ext r
    change r • (m + n) - (MulOpposite.op r : Rᵐᵒᵖ) • (m + n) =
      (r • m - (MulOpposite.op r : Rᵐᵒᵖ) • m) +
        (r • n - (MulOpposite.op r : Rᵐᵒᵖ) • n)
    simp only [smul_add]
    abel
  map_smul' a m := by
    apply Subtype.ext
    ext r
    change r • (a • m) - (MulOpposite.op r : Rᵐᵒᵖ) • (a • m) =
      a • (r • m - (MulOpposite.op r : Rᵐᵒᵖ) • m)
    simp only [smul_sub]
    rw [smul_comm r a m, smul_comm (MulOpposite.op r : Rᵐᵒᵖ) a m]

/-- Weibel's module `PDer_k(R,M)` of principal derivations. -/
noncomputable def principalDerivations : Submodule k (HochschildDerivation k R M) :=
  LinearMap.range (principalDerivationMap k R M)

end LeanCategories.Homological
