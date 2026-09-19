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
    ext q
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
def comp (S : PosetPath Q x y) (T : PosetPath Q y z) : PosetPath Q x z where
  chain :=
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
    exact hq.elim (S.source_le q) (fun h ↦ (S.le_target y S.target_mem).trans (T.source_le q h))
  le_target q hq := by
    simp only [Finset.mem_union] at hq
    exact hq.elim (fun h ↦ (S.le_target q h).trans (T.source_le y T.source_mem)) (T.le_target q)

@[simp]
lemma identity_comp (S : PosetPath Q x y) : comp (identity x) S = S := by
  ext q
  simp only [comp, identity, Finset.mem_union, Finset.mem_singleton]
  exact or_iff_right_of_imp (fun h ↦ h ▸ S.source_mem)

@[simp]
lemma comp_identity (S : PosetPath Q x y) : comp S (identity y) = S := by
  ext q
  simp only [comp, identity, Finset.mem_union, Finset.mem_singleton]
  exact or_iff_left_of_imp (fun h ↦ h ▸ S.target_mem)

@[simp]
lemma comp_assoc (R : PosetPath Q w x) (S : PosetPath Q x y) (T : PosetPath Q y z) :
    comp (comp R S) T = comp R (comp S T) := by
  ext q
  simp only [comp, Finset.mem_union]
  tauto

end PosetPath

/-- Kerodon's strict path bicategory `Path_(2)[Q]`. -/
def PathBicategory := Q

namespace PathBicategory

instance : Quiver (PathBicategory Q) where
  Hom x y := PosetPath Q x y

instance : CategoryStruct (PathBicategory Q) where
  id x := PosetPath.identity x
  comp S T := PosetPath.comp S T

instance (x y : PathBicategory Q) : SmallCategory (x ⟶ y) := inferInstance

instance : Bicategory (PathBicategory Q) where
  homCategory := fun _ _ ↦ inferInstance
  whiskerLeft S η := homOfLE <| by
    intro q hq
    simp only [CategoryStruct.comp, PosetPath.comp, Finset.mem_union] at hq ⊢
    exact hq.elim Or.inl (fun h ↦ Or.inr (η.le h))
  whiskerRight η T := homOfLE <| by
    intro q hq
    simp only [CategoryStruct.comp, PosetPath.comp, Finset.mem_union] at hq ⊢
    exact hq.elim (fun h ↦ Or.inl (η.le h)) Or.inr
  associator R S T := eqToIso (PosetPath.comp_assoc R S T)
  leftUnitor S := eqToIso (PosetPath.identity_comp S)
  rightUnitor S := eqToIso (PosetPath.comp_identity S)

instance : Bicategory.Strict (PathBicategory Q) where
  id_comp := PosetPath.identity_comp
  comp_id := PosetPath.comp_identity
  assoc := PosetPath.comp_assoc

end PathBicategory

end LeanCategories.CategoryTheory
