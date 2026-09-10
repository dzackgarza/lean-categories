/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Functor.Const

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Opposite

universe v u

namespace LeanCategories.CategoryTheory

/- Riehl FC03-C02-U002: the covariant hom functor represented by an initial object is
naturally constant at a singleton, and conversely. -/

variable {C : Type u} [Category.{v} C]

noncomputable def homFromInitialIso {c : C} (h : IsInitial c) :
    coyoneda.obj (op c) ≅ (Functor.const C).obj PUnit :=
  NatIso.ofComponents
    (fun X => ({
      toFun := fun _ => PUnit.unit
      invFun := fun _ => h.to X
      left_inv := fun f => h.hom_ext _ _
      right_inv := fun x => by cases x; rfl
    } : (c ⟶ X) ≃ PUnit).toIso)
    (by
      intro X Y f
      ext g
      rfl)

noncomputable def isInitialOfHomIsoPUnit {c : C}
    (e : coyoneda.obj (op c) ≅ (Functor.const C).obj PUnit) : IsInitial c :=
  IsInitial.ofUniqueHom
    (fun X => e.inv.app X PUnit.unit)
    (fun X f => by
      calc
        f = e.inv.app X (e.hom.app X f) := by
          exact (ConcreteCategory.congr_hom (e.hom_inv_id_app X) f).symm
        _ = e.inv.app X PUnit.unit := by
          congr 1)

noncomputable def isInitialEquivCoyonedaIsoConstPUnit (c : C) :
    IsInitial c ≃ (coyoneda.obj (op c) ≅ (Functor.const C).obj PUnit) :=
  Equiv.ofBijective homFromInitialIso ⟨
    fun _ _ _ => Subsingleton.elim _ _,
    fun e => by
      refine ⟨isInitialOfHomIsoPUnit e, ?_⟩
      apply Iso.ext
      ext X f
      cases e.hom.app X f
      rfl⟩

noncomputable def homToTerminalIso {c : C} (h : IsTerminal c) :
    yoneda.obj c ≅ (Functor.const Cᵒᵖ).obj PUnit :=
  NatIso.ofComponents
    (fun X => ({
      toFun := fun _ => PUnit.unit
      invFun := fun _ => h.from X.unop
      left_inv := fun f => h.hom_ext _ _
      right_inv := fun x => by cases x; rfl
    } : (X.unop ⟶ c) ≃ PUnit).toIso)
    (by
      intro X Y f
      ext g
      rfl)

noncomputable def isTerminalOfHomIsoPUnit {c : C}
    (e : yoneda.obj c ≅ (Functor.const Cᵒᵖ).obj PUnit) : IsTerminal c :=
  IsTerminal.ofUniqueHom
    (fun X => e.inv.app (op X) PUnit.unit)
    (fun X f => by
      calc
        f = e.inv.app (op X) (e.hom.app (op X) f) := by
          exact (ConcreteCategory.congr_hom (e.hom_inv_id_app (op X)) f).symm
        _ = e.inv.app (op X) PUnit.unit := by
          congr 1)

noncomputable def isTerminalEquivYonedaIsoConstPUnit (c : C) :
    IsTerminal c ≃ (yoneda.obj c ≅ (Functor.const Cᵒᵖ).obj PUnit) :=
  Equiv.ofBijective homToTerminalIso ⟨
    fun _ _ _ => Subsingleton.elim _ _,
    fun e => by
      refine ⟨isTerminalOfHomIsoPUnit e, ?_⟩
      apply Iso.ext
      ext X f
      cases e.hom.app X f
      rfl⟩

end LeanCategories.CategoryTheory
