/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.Order.NonemptyFiniteChains

/-!
# The path bicategory of a partially ordered set

For a partially ordered type `Q`, the hom-category from `x` to `y` consists of the finite
linearly ordered subsets of `Q` having least element `x` and greatest element `y`. Its order is
reverse inclusion. Identity paths are singletons and horizontal composition is union.

Source: Jacob Lurie, *Kerodon*, Construction 2.3.5.1, tag
[`00BA`](https://kerodon.net/tag/00BA) (FC17-KER-U00385).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.CategoryTheory

universe u

variable (Q : Type u) [PartialOrder Q]

/-- A finite path in `Q` from `x` to `y`: a finite chain whose least and greatest elements are
`x` and `y`. -/
@[ext]
structure PosetPath (x y : Q) where
  chain : PartialOrder.NonemptyFiniteChains Q
  source_mem : x ∈ chain.finset
  target_mem : y ∈ chain.finset
  source_le (z : Q) (hz : z ∈ chain.finset) : x ≤ z
  le_target (z : Q) (hz : z ∈ chain.finset) : z ≤ y

namespace PosetPath

variable {Q} {w x y z : Q}

/-- Path refinement is reverse inclusion, as in Kerodon's hom-posets. -/
instance : PartialOrder (PosetPath Q x y) where
  le S T := T.chain.finset ⊆ S.chain.finset
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ hST hTU := hTU.trans hST
  le_antisymm S T hST hTS := by
    apply PosetPath.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    exact Finset.Subset.antisymm hTS hST

/-- The singleton path is the identity path at an object. -/
def identity (x : Q) : PosetPath Q x x where
  chain :=
    { finset := {x}
      comparable := by simp }
  source_mem := by simp
  target_mem := by simp
  source_le := by simp_all
  le_target := by simp_all

/-- Concatenation of paths is union of their finite chains. -/
def comp (S : PosetPath Q x y) (T : PosetPath Q y z) : PosetPath Q x z := by
  classical
  exact
    { chain :=
        { finset := S.chain.finset ∪ T.chain.finset
          nonempty := ⟨x, by simp [S.source_mem]⟩
          comparable := by
            rintro ⟨a, ha⟩ ⟨b, hb⟩
            simp only [Finset.mem_union] at ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact S.chain.comparable ⟨a, ha⟩ ⟨b, hb⟩
            · exact Or.inl ((S.le_target a ha).trans (T.source_le b hb))
            · exact Or.inr ((S.le_target b hb).trans (T.source_le a ha))
            · exact T.chain.comparable ⟨a, ha⟩ ⟨b, hb⟩ }
      source_mem := by simp [S.source_mem]
      target_mem := by simp [T.target_mem]
      source_le q hq := by
        simp only [Finset.mem_union] at hq
        exact hq.elim (S.source_le q)
          (fun h ↦ (S.source_le y S.target_mem).trans (T.source_le q h))
      le_target q hq := by
        simp only [Finset.mem_union] at hq
        exact hq.elim (fun h ↦ (S.le_target q h).trans (T.le_target y T.source_mem))
          (T.le_target q) }

end PosetPath

/-- Kerodon's strict path bicategory `Path_(2)[Q]`. -/
structure PathBicategory where
  /-- The underlying element of the source partially ordered set. -/
  as : Q

namespace PathBicategory

open PosetPath

local instance : DecidableEq Q := Classical.decEq Q

@[reducible]
instance : Quiver (PathBicategory Q) where
  Hom x y := PosetPath Q x.as y.as

instance (x y : PathBicategory Q) : PartialOrder (x ⟶ y) := by
  change PartialOrder (PosetPath Q x.as y.as)
  infer_instance

@[reducible]
instance : CategoryStruct (PathBicategory Q) where
  id x := PosetPath.identity x.as
  comp S T := PosetPath.comp S T

instance posetPathHomCategory (x y : PathBicategory Q) : SmallCategory (x ⟶ y) := by
  change SmallCategory (PosetPath Q x.as y.as)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : Bicategory.{u, u} (PathBicategory Q) where
  homCategory := fun x y ↦ posetPathHomCategory Q x y
  whiskerLeft {_ _ _} S {_ _} η := homOfLE <| by
    intro q hq
    simp only [CategoryStruct.comp, PosetPath.comp, Finset.mem_union] at hq ⊢
    exact hq.elim Or.inl (fun h ↦ Or.inr (η.le h))
  whiskerRight {_ _ _} {_ _} η T := homOfLE <| by
    intro q hq
    simp only [CategoryStruct.comp, PosetPath.comp, Finset.mem_union] at hq ⊢
    exact hq.elim (fun h ↦ Or.inl (η.le h)) Or.inr
  associator R S T := eqToIso (by
    change PosetPath.comp (PosetPath.comp R S) T = PosetPath.comp R (PosetPath.comp S T)
    apply PosetPath.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    exact Finset.union_assoc _ _ _)
  leftUnitor S := eqToIso (by
    change PosetPath.comp (PosetPath.identity _) S = S
    apply PosetPath.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    change insert _ ∅ ∪ S.chain.finset = S.chain.finset
    rw [Finset.insert_union, Finset.empty_union, Finset.insert_eq_of_mem S.source_mem])
  rightUnitor S := eqToIso (by
    change PosetPath.comp S (PosetPath.identity _) = S
    apply PosetPath.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    change S.chain.finset ∪ insert _ ∅ = S.chain.finset
    rw [Finset.union_insert, Finset.union_empty, Finset.insert_eq_of_mem S.target_mem])
  whiskerLeft_id := by intros; apply Subsingleton.elim
  whiskerLeft_comp := by intros; apply Subsingleton.elim
  id_whiskerLeft := by intros; apply Subsingleton.elim
  comp_whiskerLeft := by intros; apply Subsingleton.elim
  id_whiskerRight := by intros; apply Subsingleton.elim
  comp_whiskerRight := by intros; apply Subsingleton.elim
  whiskerRight_id := by intros; apply Subsingleton.elim
  whiskerRight_comp := by intros; apply Subsingleton.elim
  whisker_assoc := by intros; apply Subsingleton.elim
  whisker_exchange := by intros; apply Subsingleton.elim
  pentagon := by intros; apply Subsingleton.elim
  triangle := by intros; apply Subsingleton.elim

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : Bicategory.Strict (PathBicategory Q) where
  id_comp := by
    intro x y S
    let S' : PosetPath Q x.as y.as := S
    change PosetPath.comp (PosetPath.identity x.as) S' = S'
    apply PosetPath.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    change insert _ ∅ ∪ S.chain.finset = S.chain.finset
    rw [Finset.insert_union, Finset.empty_union, Finset.insert_eq_of_mem S.source_mem]
  comp_id := by
    intro x y S
    let S' : PosetPath Q x.as y.as := S
    change PosetPath.comp S' (PosetPath.identity y.as) = S'
    apply PosetPath.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    change S.chain.finset ∪ insert _ ∅ = S.chain.finset
    rw [Finset.union_insert, Finset.union_empty, Finset.insert_eq_of_mem S.target_mem]
  assoc := by
    intro w x y z R S T
    let R' : PosetPath Q w.as x.as := R
    let S' : PosetPath Q x.as y.as := S
    let T' : PosetPath Q y.as z.as := T
    change PosetPath.comp (PosetPath.comp R' S') T' =
      PosetPath.comp R' (PosetPath.comp S' T')
    apply PosetPath.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    exact Finset.union_assoc _ _ _
  leftUnitor_eqToIso := by intros; apply Iso.ext; apply Subsingleton.elim
  rightUnitor_eqToIso := by intros; apply Iso.ext; apply Subsingleton.elim
  associator_eqToIso := by intros; apply Iso.ext; apply Subsingleton.elim

end PathBicategory

end LeanCategories.CategoryTheory
