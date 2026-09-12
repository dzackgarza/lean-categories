/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.PontryaginDual

/-!
# The Pontryagin evaluation map

Weibel, *An Introduction to Homological Algebra* (1994), §3.2, pp. 68--72,
FC05-C03-U015.

For left `R`-modules `A` and `M` over an arbitrary associative ring, this file constructs
the natural map

`A* ⊗_R M → Hom_R(M,A)*`, `f ⊗ m ↦ (h ↦ f(h m))`.

The assertion that this map is an isomorphism for finitely presented `M` is Lemma 3.2.6 and
belongs to the theorem sweep.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits
open scoped TensorProduct

universe u v w

/-- The target character module `Hom_R(M,A)*` of Weibel's evaluation map. -/
def homPontryaginDual (R : Type u) [Ring R]
    (M : ModuleCat.{v} R) (A : ModuleCat.{w} R) : ModuleCat ℤ :=
  ModuleCat.of ℤ (CharacterModule (M →ₗ[R] A))

/-- Forget the `ModuleCat` wrapper on the source Pontryagin dual. -/
def pontryaginDualOfObj (R : Type u) [Ring R] (A : ModuleCat.{w} R)
    (f : (pontryaginDualModuleObj R A : Type w)) : PontryaginDual R A := by
  change PontryaginDual R A at f
  exact f

@[simp]
theorem pontryaginDualOfObj_smul (R : Type u) [Ring R] (A : ModuleCat.{w} R)
    (r : R) (f : (pontryaginDualModuleObj R A : Type w)) :
    pontryaginDualOfObj R A ((MulOpposite.op r : Rᵐᵒᵖ) • f) =
      (MulOpposite.op r : Rᵐᵒᵖ) • pontryaginDualOfObj R A f :=
  rfl

/-- Evaluate `h : M → A` at `m` and then apply the Pontryagin character `f`. -/
def evaluationCharacter (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R)
    (f : (pontryaginDualModuleObj R A : Type w)) (m : M) :
    CharacterModule (M →ₗ[R] A) where
  toFun h := PontryaginDual.eval R (pontryaginDualOfObj R A f) (h m)
  map_zero' := by
    simpa using PontryaginDual.eval_zero_input R (pontryaginDualOfObj R A f)
  map_add' h h' := by
    simpa using PontryaginDual.eval_add_input R (pontryaginDualOfObj R A f) (h m) (h' m)

/-- The integral-bilinear pairing underlying Weibel's evaluation map. -/
def evaluationBilin (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R) :
    (pontryaginDualModuleObj R A : Type w) →ₗ[ℤ]
      M →ₗ[ℤ] CharacterModule (M →ₗ[R] A) :=
  LinearMap.mk₂ ℤ (evaluationCharacter R A M)
    (by intro f g m; ext h; rfl)
    (by intro n f m; ext h; rfl)
    (by
      intro f m m'
      ext h
      change PontryaginDual.eval R (pontryaginDualOfObj R A f) (h (m + m')) =
        PontryaginDual.eval R (pontryaginDualOfObj R A f) (h m) +
          PontryaginDual.eval R (pontryaginDualOfObj R A f) (h m')
      rw [h.map_add]
      exact PontryaginDual.eval_add_input R _ _ _)
    (by
      intro n f m
      ext h
      change PontryaginDual.eval R (pontryaginDualOfObj R A f) (h (n • m)) =
        n • PontryaginDual.eval R (pontryaginDualOfObj R A f) (h m)
      have hm : h (n • m) = n • h m := h.toAddMonoidHom.map_zsmul n m
      rw [hm]
      exact PontryaginDual.eval_zsmul_input R n _ _)

/-- The induced map on the underlying integral tensor product. -/
def evaluationLift (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R) :
    ((pontryaginDualModuleObj R A : Type w) ⊗[ℤ] M) →ₗ[ℤ]
      CharacterModule (M →ₗ[R] A) :=
  TensorProduct.lift (evaluationBilin R A M)

@[simp]
theorem evaluationLift_tmul (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R)
    (f : (pontryaginDualModuleObj R A : Type w)) (m : M) :
    evaluationLift R A M (f ⊗ₜ[ℤ] m) = evaluationCharacter R A M f m :=
  rfl

theorem evaluationCharacter_balanced (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R)
    (f : (pontryaginDualModuleObj R A : Type w)) (r : R) (m : M) :
    evaluationCharacter R A M ((MulOpposite.op r : Rᵐᵒᵖ) • f) m =
      evaluationCharacter R A M f (r • m) := by
  apply CharacterModule.ext
  intro h
  change PontryaginDual.eval R
      (pontryaginDualOfObj R A ((MulOpposite.op r : Rᵐᵒᵖ) • f)) (h m) =
        PontryaginDual.eval R (pontryaginDualOfObj R A f) (h (r • m))
  rw [pontryaginDualOfObj_smul, PontryaginDual.eval_smul, h.map_smul]

theorem evaluationLift_balanced (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R) :
    balancedRelations R (pontryaginDualModuleObj R A) M ≤
      LinearMap.ker (evaluationLift R A M) := by
  rw [balancedRelations]
  apply Submodule.span_le.2
  intro x hx
  rcases hx with ⟨f, r, m, rfl⟩
  change evaluationLift R A M
      (((MulOpposite.op r : Rᵐᵒᵖ) • f) ⊗ₜ[ℤ] m - f ⊗ₜ[ℤ] (r • m)) = 0
  rw [map_sub, evaluationLift_tmul, evaluationLift_tmul,
    evaluationCharacter_balanced, sub_self]

/-- Weibel's natural evaluation map `A* ⊗_R M → Hom_R(M,A)*`. -/
noncomputable def evaluationMap (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R) :
    relativeTensorModule R (pontryaginDualModuleObj R A) M ⟶ homPontryaginDual R M A :=
  ModuleCat.ofHom <|
    (balancedRelations R (pontryaginDualModuleObj R A) M).liftQ
      (evaluationLift R A M) (evaluationLift_balanced R A M)

end LeanCategories.Homological
