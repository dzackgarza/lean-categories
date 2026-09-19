/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.PathBicategory
public import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# The canonical lax functor to the path bicategory

For a partially ordered set `Q`, Kerodon's canonical strictly unitary lax functor sends an
order relation `x ≤ y` to the path with vertices `{x, y}`. Its composition constraint is the
reverse-inclusion morphism from `{x, y} ∪ {y, z}` to `{x, z}`.

Source: Jacob Lurie, *Kerodon*, Construction 2.3.5.4, tag
[`00BC`](https://kerodon.net/tag/00BC) (FC17-KER-U00387).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.CategoryTheory

universe u

variable {Q : Type u} [PartialOrder Q]

/-- The path associated to an order relation: its vertices are its two endpoints. -/
private noncomputable def posetPathOfLE {x y : Q} (h : x ≤ y) : PosetPath Q x y := by
  classical
  exact {
    chain :=
    { finset := {x, y}
      comparable := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl le_rfl
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl le_rfl }
    source_mem := by simp
    target_mem := by simp
    source_le z hz := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      exact hz.elim (fun hzx ↦ hzx ▸ le_rfl) (fun hzy ↦ hzy ▸ h)
    le_target z hz := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      exact hz.elim (fun hzx ↦ hzx ▸ h) (fun hzy ↦ hzy ▸ le_rfl) }

/-- Kerodon's canonical strictly unitary lax functor
`T_Q : Q → Path_(2)[Q]`.

The source category is regarded as a locally discrete bicategory. -/
def posetPathLaxFunctor :
    StrictlyUnitaryLaxFunctor (LocallyDiscrete Q) (PathBicategory Q) :=
  StrictlyUnitaryLaxFunctor.mk'
    { obj := fun x ↦ ⟨x.as⟩
      map := fun f ↦ posetPathOfLE f.as.le
      map_id := by
        intro x
        apply PosetPath.ext
        apply PartialOrder.NonemptyFiniteChains.ext
        simp [posetPathOfLE, PosetPath.identity]
      map₂ := fun η ↦ eqToHom <|
        congrArg (fun f ↦ posetPathOfLE f.as.le) (LocallyDiscrete.eq_of_hom η)
      map₂_id := by intros; apply Subsingleton.elim
      map₂_comp := by intros; apply Subsingleton.elim
      mapComp := fun f g ↦ homOfLE <| by
        intro q hq
        simp only [posetPathOfLE, Finset.mem_insert, Finset.mem_singleton] at hq
        simp only [CategoryStruct.comp, PosetPath.comp, posetPathOfLE,
          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        rcases hq with rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      mapComp_naturality_left := by intros; apply Subsingleton.elim
      mapComp_naturality_right := by intros; apply Subsingleton.elim
      map₂_leftUnitor := by intros; apply Subsingleton.elim
      map₂_rightUnitor := by intros; apply Subsingleton.elim
      map₂_associator := by intros; apply Subsingleton.elim }

end LeanCategories.CategoryTheory
