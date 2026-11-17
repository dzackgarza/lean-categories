/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Core
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A `C₂`-action is core-valued, and the two bridges to `End` of the core

`FOUNDATIONS.md` Definition 28.4 says that a `G`-action on a lattice is a functor `BG → Lat_R^≃`,
i.e. an action *into the core*, and its foundations audit insists on that codomain. For `G = C₂`
this costs nothing: the generator satisfies `ρ σ * ρ σ = 1`, and an involutive endomorphism of any
category is invertible (`isIso_gen`). So every `C₂`-action in `C` is an action in the core, and
`toCoreAction` performs the change of codomain on the nose — the underlying object does not move,
because `Core C` has the same objects as `C`.

`End X` in this Mathlib revision is a *structure* wrapping `X ⟶ X` (not an abbreviation), so the two
directions between `End ⟨X⟩` and `X ≅ X` are `End.of ∘ CoreHom.mk` and `·.asHom.iso`. Naming them
here is what lets an involution of a lattice be read as an element of the monoid `End ⟨X⟩` and back.

## Provenance

Searched in Mathlib at the pinned revision: `IsIso` of an involutive endomorphism
(`isIso_of_comp_self`, `isIso_of_mul_self_eq_one`, `End.isUnit_iff_isIso`, `Groupoid`),
`End.of`/`End.asHom`/`End.mul_asHom`/`End.one_asHom`, `asIso`/`asIso_hom`, `Action.ρAut`. Mathlib
has `End.isUnit_iff_isIso` and nothing that turns `f * f = 1` into `IsIso f.asHom`; `Action` is a
root-namespace structure with `V` and `ρ`, and no API moves an action between `C` and `Core C`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe v u

/-- The two elements of `ZMod 2`. Proved through `ZMod.val` rather than `decide`: in a `module`
file the `Fintype (Multiplicative (ZMod 2))` instance is not found by instance search for the
decidable `∀`, so a `decide` proof of the quantified statement does not elaborate. -/
theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt : x.val < 2 := ZMod.val_lt x
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
  · left
    exact (ZMod.val_eq_zero x).mp (Nat.lt_one_iff.mp h)
  · right
    exact (ZMod.val_eq_one (by norm_num) x).mp h

/-- The two elements of `C₂`. -/
theorem C2.eq_one_or_gen (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  rcases zmod_two_eq_zero_or_one (Multiplicative.toAdd g) with h | h
  · left
    rw [show g = Multiplicative.ofAdd (Multiplicative.toAdd g) from rfl, h]
    simp
  · right
    rw [show g = Multiplicative.ofAdd (Multiplicative.toAdd g) from rfl, h]

/-- The generator is not the identity of `C₂`. -/
theorem C2.gen_ne_one : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide

/-- The generator squares to the identity of `C₂`. -/
theorem C2.gen_mul_self :
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide

namespace CategoryTheory.Core

variable {C : Type u} [Category.{v} C] {X : C}

/-- The element of `End ⟨X⟩` in the core that an automorphism of `X` defines. -/
def endOfIso (e : X ≅ X) : End (⟨X⟩ : Core C) :=
  End.of (CoreHom.mk e)

/-- The automorphism of `X` that an endomorphism of `⟨X⟩` in the core defines. -/
def isoOfEnd (e : End (⟨X⟩ : Core C)) : X ≅ X :=
  e.asHom.iso

@[simp]
theorem isoOfEnd_endOfIso (e : X ≅ X) : isoOfEnd (endOfIso e) = e := rfl

/-- An involutive automorphism of `X` is an involutive element of the endomorphism monoid of `⟨X⟩`
in the core. -/
theorem endOfIso_mul_self (e : X ≅ X) (he : e ≪≫ e = Iso.refl X) :
    endOfIso e * endOfIso e = 1 := by
  apply End.ext
  rw [End.mul_asHom, End.one_asHom]
  apply Core.hom_ext
  change (endOfIso e).asHom.iso.hom ≫ (endOfIso e).asHom.iso.hom = 𝟙 X
  rw [show (endOfIso e).asHom.iso = e from rfl, ← Iso.trans_hom, he]
  rfl

end CategoryTheory.Core

namespace CategoryTheory

namespace Action

variable {C : Type u} [Category.{v} C]

/-- The generator of `C₂` acts by an involutive endomorphism. -/
theorem mul_self_gen (A : Action C (Multiplicative (ZMod 2))) :
    A.ρ (Multiplicative.ofAdd 1) * A.ρ (Multiplicative.ofAdd 1) = 1 := by
  have hgen : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) * Multiplicative.ofAdd 1 = 1 :=
    by decide
  rw [← map_mul, hgen, map_one]

/-- **A `C₂`-action is core-valued.** The generator of `C₂` acts by an involutive endomorphism,
and an involutive endomorphism is invertible: `IsIso` is witnessed by the endomorphism itself. -/
theorem isIso_gen (A : Action C (Multiplicative (ZMod 2))) :
    IsIso (A.ρ (Multiplicative.ofAdd 1)).asHom := by
  have h := mul_self_gen A
  have h2 := congrArg End.asHom h
  rw [End.mul_asHom, End.one_asHom] at h2
  exact IsIso.mk ⟨_, h2, h2⟩

/-- The generator's square as a composable equation. -/
theorem comp_self_gen (A : Action C (Multiplicative (ZMod 2))) :
    (A.ρ (Multiplicative.ofAdd 1)).asHom ≫ (A.ρ (Multiplicative.ofAdd 1)).asHom = 𝟙 A.V := by
  have h2 := congrArg End.asHom (mul_self_gen A)
  rwa [End.mul_asHom, End.one_asHom] at h2

/-- The isomorphism of `A.V` by which the generator of `C₂` acts. -/
def genIso (A : Action C (Multiplicative (ZMod 2))) : A.V ≅ A.V := by
  haveI := isIso_gen A
  exact asIso (A.ρ (Multiplicative.ofAdd 1)).asHom

@[simp]
theorem genIso_hom (A : Action C (Multiplicative (ZMod 2))) :
    (genIso A).hom = (A.ρ (Multiplicative.ofAdd 1)).asHom := by
  simp [genIso]

/-- **Every `C₂`-action in `C` is an action in the core, on the same object.** The underlying object
does not move (`(toCoreAction A).V.of = A.V` definitionally); only the codomain of `ρ` changes,
which `isIso_gen` makes possible. -/
def toCoreAction (A : Action C (Multiplicative (ZMod 2))) :
    Action (Core C) (Multiplicative (ZMod 2)) where
  V := ⟨A.V⟩
  ρ :=
    { toFun := fun g =>
        if g = 1 then 1 else Core.endOfIso (genIso A)
      map_one' := by simp
      map_mul' := by
        have hsq : Core.endOfIso (genIso A) * Core.endOfIso (genIso A) = 1 := by
          apply End.ext
          rw [End.mul_asHom, End.one_asHom]
          apply Core.hom_ext
          change (genIso A).hom ≫ (genIso A).hom = 𝟙 A.V
          exact comp_self_gen A
        intro a b
        rcases C2.eq_one_or_gen a with rfl | rfl <;> rcases C2.eq_one_or_gen b with rfl | rfl
        · simp
        · simp
        · simp
        · rw [C2.gen_mul_self]
          simp [hsq] }

@[simp]
theorem toCoreAction_V (A : Action C (Multiplicative (ZMod 2))) : (toCoreAction A).V.of = A.V :=
  rfl

/-- Two `Action`-objects with the same underlying object and equal `ρ` are equal. `Action` has no
`ext` lemma of its own because its second field depends on the first. -/
theorem ext' {V : Type*} [Category V] {G : Type*} [Monoid G]
    {A B : Action V G} (hV : A.V = B.V) (hρ : HEq A.ρ B.ρ) : A = B := by
  cases A with
  | mk VA ρA =>
    cases B with
    | mk VB ρB =>
      cases hV
      exact congrArg (Action.mk (V := V) (G := G) VA) (eq_of_heq hρ)

end Action

end CategoryTheory
