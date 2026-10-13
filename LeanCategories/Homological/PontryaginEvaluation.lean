/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.NoncommutativeTensor
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Module.Hom

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

/-- The generic domain action on additive homomorphisms gives the character module of a left
`R`-module its source right `R`-module structure.  This is interface glue only: the action is
Mathlib's `DomMulAct` action `(f · r)(a) = f(r • a)`. -/
instance characterModuleRightModule (R : Type u) [Ring R] (A : Type w)
    [AddCommGroup A] [Module R A] : Module Rᵐᵒᵖ (CharacterModule A) := by
  change Module (DomMulAct R) (A →+ AddCircle (1 : ℚ))
  infer_instance

/-- Evaluate `h : M → A` at `m` and then apply the Pontryagin character `f`. -/
def evaluationCharacter (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R)
    (f : CharacterModule A) (m : M) :
    CharacterModule (M →ₗ[R] A) where
  toFun h := f (h m)
  map_zero' := by simp
  map_add' h h' := by simp

/-- The integral-bilinear pairing underlying Weibel's evaluation map. -/
def evaluationBilin (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R) :
    CharacterModule A →ₗ[ℤ]
      M →ₗ[ℤ] CharacterModule (M →ₗ[R] A) :=
  LinearMap.mk₂ ℤ (evaluationCharacter R A M)
    (by intro f g m; ext h; rfl)
    (by intro n f m; ext h; rfl)
    (by
      intro f m m'
      ext h
      change f (h (m + m')) = f (h m) + f (h m')
      rw [h.map_add, map_add])
    (by
      intro n f m
      ext h
      change f (h (n • m)) = n • f (h m)
      rw [map_zsmul h, map_zsmul f])

/-- The induced map on the underlying integral tensor product. -/
def evaluationLift (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R) :
    (CharacterModule A ⊗[ℤ] M) →ₗ[ℤ]
      CharacterModule (M →ₗ[R] A) :=
  TensorProduct.lift (evaluationBilin R A M)

@[simp]
theorem evaluationLift_tmul (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R)
    (f : CharacterModule A) (m : M) :
    evaluationLift R A M (f ⊗ₜ[ℤ] m) = evaluationCharacter R A M f m :=
  rfl

theorem evaluationCharacter_balanced (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R)
    (f : CharacterModule A) (r : R) (m : M) :
    evaluationCharacter R A M ((MulOpposite.op r : Rᵐᵒᵖ) • f) m =
      evaluationCharacter R A M f (r • m) := by
  apply CharacterModule.ext
  intro h
  change ((MulOpposite.op r : Rᵐᵒᵖ) • f) (h m) = f (h (r • m))
  rw [h.map_smul]
  rfl

theorem evaluationLift_balanced (R : Type u) [Ring R]
    (A : ModuleCat.{w} R) (M : ModuleCat.{v} R) :
    balancedRelations R (ModuleCat.of Rᵐᵒᵖ (CharacterModule A)) M ≤
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
    relativeTensorModule R (ModuleCat.of Rᵐᵒᵖ (CharacterModule A)) M ⟶
      ModuleCat.of ℤ (CharacterModule (M →ₗ[R] A)) :=
  ModuleCat.ofHom <|
    (balancedRelations R (ModuleCat.of Rᵐᵒᵖ (CharacterModule A)) M).liftQ
      (evaluationLift R A M) (evaluationLift_balanced R A M)

end LeanCategories.Homological
