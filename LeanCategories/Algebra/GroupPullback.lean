/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.GroupProduct
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

@[expose] public section

/-!
# Pullbacks in `Grp`, and the intersection of subgroups as a pullback

The pullback of `f : G ⟶ K` and `g : H ⟶ K` in `GrpCat`, on the subgroup of `G × H` of the pairs
`(x, y)` with `f x = g y`, with its two projections and its universal property
(`groupPullbackIsLimit`). The intersection `P ⊓ Q` of two subgroups, with its two inclusions, is
the pullback of `P.subtype` and `Q.subtype` over `G` (`subgroupIntersectionIsLimit`), and the
chosen pullback of the two inclusions is that intersection up to isomorphism
(`subgroupIntersectionIsoGroupPullback`). This is the consumer item "group pullbacks and subgroup
intersections" of lean-categories#91.

## LC-09 search record

Corpus queries (formalization-corpus API, whole index): `pullback GrpCat` (0 files),
`group pullback subgroup intersection` (0 files), `PullbackCone GrpCat MonoidHom` (0 files).
Nothing to port. Local Mathlib hits, all Apache-2.0, inspected at the pinned head:
`PullbackCone.mk` and `PullbackCone.IsLimit.mk`
(`Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean:119` and `:203`),
`Subgroup.inclusion` (`Mathlib/Algebra/Group/Subgroup/Defs.lean:581`), `Subgroup.mem_inf`
(`Mathlib/Algebra/Group/Subgroup/Lattice.lean:233`), `MonoidHom.prod` and `MonoidHom.codRestrict`
(`Mathlib/Algebra/Group/Prod.lean`, `Mathlib/Algebra/Group/Submonoid/Operations.lean`).

## Main declarations

* `pullbackSubgroup`, `groupPullback`, `groupPullbackFst`, `groupPullbackSnd`;
* `groupPullbackCone`, `groupPullbackIsLimit`, `groupPullbackLimitCone`;
* `subgroupIntersectionCone`, `subgroupIntersectionIsLimit`,
  `subgroupIntersectionIsoGroupPullback`.
-/

open CategoryTheory Limits

namespace LeanCategories.Algebra

universe u

variable {G H K : GrpCat.{u}}

/-- The subgroup of `G × H` of the pairs `(x, y)` with `f x = g y`. -/
def pullbackSubgroup (f : G ⟶ K) (g : H ⟶ K) : Subgroup (G × H) where
  carrier := {p | f.hom p.1 = g.hom p.2}
  one_mem' := by
    change f.hom (1 : G) = g.hom (1 : H)
    rw [map_one, map_one]
  mul_mem' := by
    intro a b ha hb
    change f.hom (a.1 * b.1) = g.hom (a.2 * b.2)
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change f.hom a.1⁻¹ = g.hom a.2⁻¹
    rw [map_inv, map_inv, ha]

/-- The pullback of `f` and `g` in `Grp`, on the pairs with equal images. -/
def groupPullback (f : G ⟶ K) (g : H ⟶ K) : GrpCat.{u} :=
  GrpCat.of ↥(pullbackSubgroup f g)

/-- The first projection of the pullback. -/
def groupPullbackFst (f : G ⟶ K) (g : H ⟶ K) : groupPullback f g ⟶ G :=
  GrpCat.ofHom ((MonoidHom.fst G H).comp (pullbackSubgroup f g).subtype)

/-- The second projection of the pullback. -/
def groupPullbackSnd (f : G ⟶ K) (g : H ⟶ K) : groupPullback f g ⟶ H :=
  GrpCat.ofHom ((MonoidHom.snd G H).comp (pullbackSubgroup f g).subtype)

/-- The two projections of the pullback agree after composing with `f` and `g`. -/
theorem groupPullbackFst_comp (f : G ⟶ K) (g : H ⟶ K) :
    groupPullbackFst f g ≫ f = groupPullbackSnd f g ≫ g := by
  ext p
  exact p.2

/-- The pullback cone of `f` and `g`. -/
def groupPullbackCone (f : G ⟶ K) (g : H ⟶ K) : PullbackCone f g :=
  PullbackCone.mk (groupPullbackFst f g) (groupPullbackSnd f g) (groupPullbackFst_comp f g)

/-- The pullback cone is a limit cone. -/
def groupPullbackIsLimit (f : G ⟶ K) (g : H ⟶ K) :
    IsLimit (groupPullbackCone f g) := by
  unfold groupPullbackCone
  refine PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_)
  · exact GrpCat.ofHom ((MonoidHom.prod s.fst.hom s.snd.hom).codRestrict _
      (fun x => by
        change f.hom (s.fst.hom x) = g.hom (s.snd.hom x)
        simpa using ConcreteCategory.congr_hom s.condition x))
  · ext x
    rfl
  · ext x
    rfl
  · ext x
    apply Subtype.ext
    exact Prod.ext (ConcreteCategory.congr_hom h₁ x) (ConcreteCategory.congr_hom h₂ x)

/-- The pullback of `f` and `g`, as a limit cone of the cospan they form. -/
def groupPullbackLimitCone (f : G ⟶ K) (g : H ⟶ K) : LimitCone (cospan f g) :=
  ⟨groupPullbackCone f g, groupPullbackIsLimit f g⟩

section Intersection

variable {G : GrpCat.{u}} (P Q : Subgroup G)

/-- The intersection `P ⊓ Q` with its two inclusions as a cone over the cospan
`P ⟶ G ⟵ Q`. -/
def subgroupIntersectionCone :
    PullbackCone (GrpCat.ofHom P.subtype) (GrpCat.ofHom Q.subtype) :=
  PullbackCone.mk (GrpCat.ofHom (Subgroup.inclusion inf_le_left))
    (GrpCat.ofHom (Subgroup.inclusion inf_le_right)) (by ext x; rfl)

/-- The intersection of two subgroups is their pullback over `G`. -/
def subgroupIntersectionIsLimit : IsLimit (subgroupIntersectionCone P Q) := by
  unfold subgroupIntersectionCone
  refine PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_)
  · refine GrpCat.ofHom ((P.subtype.comp s.fst.hom).codRestrict _ (fun x => ?_))
    refine ⟨(s.fst.hom x).2, ?_⟩
    have hx := ConcreteCategory.congr_hom s.condition x
    exact hx ▸ (s.snd.hom x).2
  · ext x
    rfl
  · ext x
    change ((s.fst.hom x : G)) = ((s.snd.hom x : G))
    simpa using ConcreteCategory.congr_hom s.condition x
  · ext x
    change ((m.hom x : G)) = ((s.fst.hom x : G))
    simpa using congrArg Subtype.val (ConcreteCategory.congr_hom h₁ x)

/-- The chosen pullback of the two subgroup inclusions is the intersection. -/
noncomputable def subgroupIntersectionIsoGroupPullback :
    groupPullback (GrpCat.ofHom P.subtype) (GrpCat.ofHom Q.subtype) ≅ GrpCat.of ↥(P ⊓ Q) :=
  (groupPullbackIsLimit (GrpCat.ofHom P.subtype) (GrpCat.ofHom Q.subtype)).conePointUniqueUpToIso
    (subgroupIntersectionIsLimit P Q)

end Intersection

end LeanCategories.Algebra
