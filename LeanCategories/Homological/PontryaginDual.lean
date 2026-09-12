/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.NoncommutativeTensor
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Module.Hom

/-!
# Pontryagin duals and the tensor-Hom evaluation map

Weibel, *An Introduction to Homological Algebra* (1994), Definition 3.2.3 and the construction
following it, §3.2, pp. 77--80 (FC05-C03-U011 and FC05-C03-U015).

For a left module `B` over an arbitrary associative ring `R`, the Pontryagin dual is the abelian
group `Hom_ℤ(B, ℚ/ℤ)` with right action `(f r)(b) = f(r b)`.  We then construct Weibel's natural
evaluation map `A* ⊗_R M → Hom_R(M,A)*`.  The assertion that this map is an isomorphism for
finitely presented `M` is result-level material and is intentionally not included here.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits
open scoped TensorProduct

universe u v w

/-- The Pontryagin dual `B* = Hom_ℤ(B, ℚ/ℤ)` of a left `R`-module.

The ring parameter is retained in the type so that the source right `R`-module structure can be
installed without changing Mathlib's global `CharacterModule` instances.

Source: Weibel, Definition 3.2.3, pp. 77--80 (FC05-C03-U011). -/
def PontryaginDual (R : Type u) [Ring R] (B : Type v)
    [AddCommGroup B] [Module R B] : Type v :=
  CharacterModule B

instance pontryaginDualAddCommGroup (R : Type u) [Ring R] (B : Type v)
    [AddCommGroup B] [Module R B] : AddCommGroup (PontryaginDual R B) := by
  unfold PontryaginDual CharacterModule
  infer_instance

/-- The source right action `(f r)(b) = f(r b)`, represented as a left `Rᵐᵒᵖ`-action. -/
instance pontryaginDualModule (R : Type u) [Ring R] (B : Type v)
    [AddCommGroup B] [Module R B] : Module Rᵐᵒᵖ (PontryaginDual R B) := by
  unfold PontryaginDual CharacterModule
  change Module (DomMulAct R) (B →+ AddCircle (1 : ℚ))
  infer_instance

/-- Forget the source right-module structure and view a Pontryagin dual as Mathlib's underlying
character module. -/
def PontryaginDual.toCharacter (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (f : PontryaginDual R B) : CharacterModule B := by
  change CharacterModule B at f
  exact f

/-- Evaluation of a Pontryagin character. -/
def PontryaginDual.eval (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (f : PontryaginDual R B) (b : B) : AddCircle (1 : ℚ) := by
  exact (PontryaginDual.toCharacter R f) b

@[simp]
theorem PontryaginDual.eval_zero (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (b : B) :
    PontryaginDual.eval R (0 : PontryaginDual R B) b = 0 :=
  rfl

@[simp]
theorem PontryaginDual.eval_smul (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (r : R) (f : PontryaginDual R B) (b : B) :
    PontryaginDual.eval R ((MulOpposite.op r : Rᵐᵒᵖ) • f) b =
      PontryaginDual.eval R f (r • b) :=
  rfl

@[simp]
theorem PontryaginDual.eval_add (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (f g : PontryaginDual R B) (b : B) :
    PontryaginDual.eval R (f + g) b =
      PontryaginDual.eval R f b + PontryaginDual.eval R g b :=
  rfl

@[simp]
theorem PontryaginDual.eval_add_input (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (f : PontryaginDual R B) (b b' : B) :
    PontryaginDual.eval R f (b + b') =
      PontryaginDual.eval R f b + PontryaginDual.eval R f b' :=
  map_add (PontryaginDual.toCharacter R f) b b'

@[simp]
theorem PontryaginDual.eval_zero_input (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (f : PontryaginDual R B) :
    PontryaginDual.eval R f (0 : B) = 0 :=
  map_zero (PontryaginDual.toCharacter R f)

@[simp]
theorem PontryaginDual.eval_zsmul (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (n : ℤ) (f : PontryaginDual R B) (b : B) :
    PontryaginDual.eval R (n • f) b = n • PontryaginDual.eval R f b := by
  rfl

@[simp]
theorem PontryaginDual.eval_zsmul_input (R : Type u) [Ring R] {B : Type v}
    [AddCommGroup B] [Module R B] (n : ℤ) (f : PontryaginDual R B) (b : B) :
    PontryaginDual.eval R f (n • b) = n • PontryaginDual.eval R f b :=
  map_zsmul (PontryaginDual.toCharacter R f) n b

/-- The Pontryagin dual as a right `R`-module object. -/
def pontryaginDualModuleObj (R : Type u) [Ring R] (B : ModuleCat.{v} R) :
    ModuleCat.{v} Rᵐᵒᵖ :=
  ModuleCat.of Rᵐᵒᵖ (PontryaginDual R B)

end LeanCategories.Homological
