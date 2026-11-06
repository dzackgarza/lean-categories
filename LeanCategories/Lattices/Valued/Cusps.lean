/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantAction
public import Mathlib.GroupTheory.Index

/-!
# The `(L, Γ)` cusp category (#113)

Stage 1 of the lattice pipeline: for an integral lattice `L` and a **finite-index** subgroup
`Γ ⊆ O(L)`, the cusps of `Γ` are the `Γ`-orbits of primitive isotropic sublattices of `L`, by rank:
rank 1 gives the 0-cusps and rank 2 the 1-cusps.

`Modules.Bilinear.Valued.BilinModuleCat.IsFiniteIndexEmbedding` is a bare predicate about a single
embedding. What the class needs is a subgroup of the orthogonal group that carries its finiteness
witness as data, which is `FiniteIndexSubgroup` below, built on Mathlib's `Subgroup.FiniteIndex`.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] {W : Type u} [AddCommGroup W] [Module R W]

/-- A subgroup of `O(L)` together with the witness that it has finite index. The index is a field,
not a separate hypothesis: a consumer of a cusp that does not know the index is finite cannot state
the finiteness results the class exists for. -/
structure FiniteIndexSubgroup (L : IntegralLatticeCat R) where
  /-- The subgroup of the orthogonal group. -/
  toSubgroup : Subgroup (OrthogonalGroup L)
  /-- Its index in `O(L)` is finite. -/
  finiteIndex : toSubgroup.FiniteIndex

namespace FiniteIndexSubgroup

variable {L : IntegralLatticeCat R}

instance : Coe (FiniteIndexSubgroup L) (Subgroup (OrthogonalGroup L)) :=
  ⟨FiniteIndexSubgroup.toSubgroup⟩

@[simp] theorem coe_mk (H : Subgroup (OrthogonalGroup L)) (h : H.FiniteIndex) :
    (⟨H, h⟩ : FiniteIndexSubgroup L).toSubgroup = H := rfl

/-- The whole orthogonal group has finite index in itself: the canonical example. -/
def top (L : IntegralLatticeCat R) : FiniteIndexSubgroup L where
  toSubgroup := ⊤
  finiteIndex := inferInstance

end FiniteIndexSubgroup

/-- An object of the cusp category: an integral lattice together with a finite-index subgroup of its
orthogonal group. -/
structure CuspObject where
  /-- The lattice `L`. -/
  lattice : IntegralLatticeCat R
  /-- The finite-index subgroup `Γ ⊆ O(L)`. -/
  gamma : FiniteIndexSubgroup lattice

/-- A morphism of the cusp category: an isometric embedding `L₁ ⟶ L₂` that carries `Γ₁` into `Γ₂`,
i.e. for every `γ ∈ Γ₁` there is `δ ∈ Γ₂` with `f ∘ γ = δ ∘ f`. -/
structure CuspMorphism (X Y : CuspObject (R := R)) where
  /-- The underlying lattice morphism. -/
  hom : X.lattice ⟶ Y.lattice
  /-- Equivariance: every `γ ∈ Γ₁` is matched by some `δ ∈ Γ₂` with `f ∘ γ = δ ∘ f`. -/
  equivariant : ∀ γ ∈ X.gamma.toSubgroup, ∃ δ ∈ Y.gamma.toSubgroup,
    (OrthogonalGroup.asLatticeIso γ).hom ≫ hom = hom ≫ (OrthogonalGroup.asLatticeIso δ).hom

namespace CuspMorphism

variable {X Y Z : CuspObject (R := R)}

/-- The identity morphism is equivariant for `γ ↦ γ`. -/
def id (X : CuspObject (R := R)) : CuspMorphism X X where
  hom := 𝟙 X.lattice
  equivariant := by
    intro γ hγ
    exact ⟨γ, hγ, by simp⟩

/-- Composition of equivariant embeddings is equivariant: the witnesses compose. -/
def comp (f : CuspMorphism X Y) (g : CuspMorphism Y Z) : CuspMorphism X Z where
  hom := f.hom ≫ g.hom
  equivariant := by
    intro γ hγ
    obtain ⟨δ, hδ, hf⟩ := f.equivariant γ hγ
    obtain ⟨ε, hε, hg⟩ := g.equivariant δ hδ
    exact ⟨ε, hε, by rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]⟩

end CuspMorphism

/-- Two cusp morphisms are equal when their underlying lattice morphisms are: the equivariance
field is a proposition. -/
@[ext] theorem CuspMorphism.ext {X Y : CuspObject (R := R)} {f g : CuspMorphism X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; congr

/-- The cusp category: objects `(L, Γ)`, morphisms `Γ`-equivariant isometric embeddings. -/
instance : Category (CuspObject (R := R)) where
  Hom X Y := CuspMorphism X Y
  id X := CuspMorphism.id X
  comp f g := CuspMorphism.comp f g
  id_comp := by intro X Y f; ext; simp [CuspMorphism.id, CuspMorphism.comp]
  comp_id := by intro X Y f; ext; simp [CuspMorphism.id, CuspMorphism.comp]
  assoc := by intro W X Y Z f g h; ext; simp [CuspMorphism.comp, Category.assoc]

end LeanCategories.Lattices.Valued
