/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.GroupPullback

@[expose] public section

/-!
# Acceptance tests for lean-categories#91: the `Grp` items

The two acceptance items that live in `Grp`, decided on the smallest input that settles each: the
symmetric groups on `Fin 2` and `Fin 3` for the product (`ProductAcceptance`), and the symmetric
group on `Fin 3` for the pullbacks and subgroup intersections (`PullbackAcceptance`).

* "Mathematics wanted" 1 — the categorical product in `Grp`, with its projections and the factor
  inclusions `G_i → G₁ × G₂` as group morphisms;
* consumer 2 — group pullbacks and subgroup intersections.

The lattice-side items of the issue (the injective orthogonal-sum map, products of subgroups of
orthogonal groups, and the family stabilizer) are decided in `Lattices/Valued/OrthogonalGroup.lean`,
`Lattices/Valued/FamilyStabilizer.lean` and the tests recorded in this file's sibling
`OrthogonalSumGroupTests`.
-/

open CategoryTheory Limits

namespace LeanCategories.Algebra

/-! ## "Mathematics wanted" 1: the categorical product in `Grp` -/

namespace ProductAcceptance

/-- The first factor: the symmetric group on `Fin 2`. -/
abbrev G : GrpCat :=
  GrpCat.of (Equiv.Perm (Fin 2))

/-- The second factor: the symmetric group on `Fin 3`. -/
abbrev H : GrpCat :=
  GrpCat.of (Equiv.Perm (Fin 3))

/-- The apex of the product cone is `G × H` on the nose. -/
theorem apex : (groupProductFan G H).pt = GrpCat.of (G × H) :=
  rfl

/-- The first projection is `Prod.fst`. -/
theorem fst_apply (x : ↥G × ↥H) : groupProductFst G H x = x.1 :=
  rfl

/-- The second projection is `Prod.snd`. -/
theorem snd_apply (x : ↥G × ↥H) : groupProductSnd G H x = x.2 :=
  rfl

/-- The mediator of the universal property is the pairing `x ↦ (f x, g x)`. -/
theorem lift_apply (f : G ⟶ G) (g : G ⟶ H) (x : ↥G) :
    (groupProductIsLimit G H).lift (BinaryFan.mk f g) x = (f x, g x) :=
  rfl

/-- The inclusion of the first factor is `x ↦ (x, 1)`. -/
theorem inl_apply (x : ↥G) : groupProductInl G H x = (x, 1) :=
  rfl

/-- The inclusion of the second factor is `y ↦ (1, y)`. -/
theorem inr_apply (y : ↥H) : groupProductInr G H y = (1, y) :=
  rfl

/-- The first inclusion is a section of the first projection and is killed by the second. -/
theorem inl_components :
    groupProductInl G H ≫ groupProductFst G H = 𝟙 G ∧
      groupProductInl G H ≫ groupProductSnd G H = (1 : G ⟶ H) :=
  ⟨groupProductInl_fst G H, groupProductInl_snd G H⟩

/-- The comparison with the limit `Limits.prod` that Mathlib chooses. -/
noncomputable def isoProd : groupProduct G H ≅ Limits.prod G H :=
  groupProductIsoProd G H

end ProductAcceptance

/-! ## Consumer 2: group pullbacks and subgroup intersections -/

namespace PullbackAcceptance

/-- A concrete group for the pullbacks: the symmetric group on `Fin 3`. -/
abbrev G : GrpCat :=
  GrpCat.of (Equiv.Perm (Fin 3))

/-- The pullback cone's apex is the subgroup of pairs with equal images. -/
theorem apex (P Q : Subgroup ↥G) :
    (groupPullbackCone (GrpCat.ofHom P.subtype) (GrpCat.ofHom Q.subtype)).pt =
      GrpCat.of ↥(pullbackSubgroup (GrpCat.ofHom P.subtype) (GrpCat.ofHom Q.subtype)) :=
  rfl

/-- The pullback of the two trivial subgroups is the trivial group: its carrier's element is the
pair `(1, 1)`, and it satisfies the pair condition by reflexivity. -/
theorem diagonal_mem :
    (⟨(1, 1), rfl⟩ : ↥(pullbackSubgroup (GrpCat.ofHom (⊥ : Subgroup ↥G).subtype)
      (GrpCat.ofHom (⊥ : Subgroup ↥G).subtype))).1 = (1, 1) :=
  rfl

/-- The intersection `P ⊓ Q` with its two inclusions is the pullback of the inclusions. -/
def intersectionLimit (P Q : Subgroup ↥G) : IsLimit (subgroupIntersectionCone P Q) :=
  subgroupIntersectionIsLimit P Q

/-- The chosen pullback of the two inclusions is the intersection itself. -/
noncomputable def intersectionIso (P Q : Subgroup ↥G) :
    groupPullback (GrpCat.ofHom P.subtype) (GrpCat.ofHom Q.subtype) ≅ GrpCat.of ↥(P ⊓ Q) :=
  subgroupIntersectionIsoGroupPullback P Q

end PullbackAcceptance

end LeanCategories.Algebra
