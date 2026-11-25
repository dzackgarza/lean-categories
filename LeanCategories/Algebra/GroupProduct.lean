/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Group.Prod

@[expose] public section

/-!
# The binary product in `Grp`

The binary product of two groups in `GrpCat` on the carrier `G × H`: its two projections, the
factor inclusions `G → G × H` and `H → G × H`, the product cone with its universal property
(`groupProductIsLimit`), and the comparison `groupProductIsoProd` with the binary product
`Limits.prod` that Mathlib's `GrpCat.hasLimits` chooses.

## Why the cone is written out

`GrpCat` is complete in Mathlib (`Mathlib/Algebra/Category/Grp/Limits.lean`, `GrpCat.hasLimits`)
but its chosen limits are not concrete products: the limit point is `Types.Small.limitCone`'s
`Shrink` of the sections of the forgetful functor, so `Limits.prod G H` is not recognisable as
`G × H` and its `prod.lift` is not the pairing `x ↦ (f x, g x)`. The repository had presented
one `Grp` limit concretely before this file — the kernel as an equalizer of `f` and `1`
(`LeanCategories.Algebra.kernelFork`, `kernelLimitCone` in `Algebra/GroupKernel.lean`,
registered as `lim.groups.kernel` in `Catalogue/Semantics/Limits/Registration.lean`) — and no
binary product, no product cone and no factor inclusions. Those are what this file adds;
`groupProductIsoProd` identifies the concrete cone with the chosen limit.

## LC-09 search record

Corpus queries (formalization-corpus API, whole index): `MonoidHom.inl GrpCat product` (0 files),
`binary product GrpCat` (24 files, none a binary product of groups), `"MonoidHom.inl"
"BinaryFan"` (0 files), `"prodCongr" isometry bilinear` (12 files, none a group-product cone),
`"orthogonalSum" isometry group product` (6 files, all LMFDB blueprint prose). Nothing to port;
the constructions below are glue over Mathlib. Local Mathlib hits, all Apache-2.0, inspected at
the pinned head: `MonoidHom.inl` (`Mathlib/Algebra/Group/Prod.lean:335`), `MonoidHom.inr`
(line 344), `MonoidHom.fst_comp_inl`, `MonoidHom.snd_comp_inl`, `MonoidHom.fst_comp_inr`,
`MonoidHom.snd_comp_inr` (lines 367–381), `MonoidHom.prod` (line 392),
`BinaryFan.IsLimit.mk` (`Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts.lean:214`),
`Limits.prodIsProd` (line 575) and `GrpCat.hasLimits`
(`Mathlib/Algebra/Category/Grp/Limits.lean`).

## Main declarations

* `groupProduct`, `groupProductFst`, `groupProductSnd`;
* `groupProductFan`, `groupProductIsLimit`;
* `groupProductInl`, `groupProductInr` with `groupProductInl_fst`, `groupProductInl_snd`,
  `groupProductInr_fst`, `groupProductInr_snd`, and the universal-property characterisations
  `eq_groupProductInl`, `eq_groupProductInr`;
* `groupProductIsoProd`.
-/

open CategoryTheory Limits

namespace LeanCategories.Algebra

universe u

variable (G H : GrpCat.{u})

/-- The product group `G × H` as an object of `Grp`. -/
def groupProduct : GrpCat.{u} :=
  GrpCat.of (G × H)

/-- The first projection `G × H ⟶ G`. -/
def groupProductFst : groupProduct G H ⟶ G :=
  GrpCat.ofHom (MonoidHom.fst G H)

/-- The second projection `G × H ⟶ H`. -/
def groupProductSnd : groupProduct G H ⟶ H :=
  GrpCat.ofHom (MonoidHom.snd G H)

/-- The product fan of `G` and `H` on the carrier `G × H`. -/
def groupProductFan : BinaryFan G H :=
  BinaryFan.mk (groupProductFst G H) (groupProductSnd G H)

/-- The product fan is a limit cone: a group morphism into `G × H` is exactly a pair of group
morphisms into `G` and `H`. -/
def groupProductIsLimit : IsLimit (groupProductFan G H) :=
  BinaryFan.IsLimit.mk _
    (fun {_T} f g => GrpCat.ofHom (f.hom.prod g.hom))
    (fun {_T} _ _ => by ext x; rfl)
    (fun {_T} _ _ => by ext x; rfl)
    (fun {_T} _ _ m h₁ h₂ => by
      ext x
      exact Prod.ext (ConcreteCategory.congr_hom h₁ x) (ConcreteCategory.congr_hom h₂ x))

/-- The inclusion of the first factor, `G ⟶ G × H`. -/
def groupProductInl : G ⟶ groupProduct G H :=
  GrpCat.ofHom (MonoidHom.inl G H)

/-- The inclusion of the second factor, `H ⟶ G × H`. -/
def groupProductInr : H ⟶ groupProduct G H :=
  GrpCat.ofHom (MonoidHom.inr G H)

/-- The first inclusion is a section of the first projection. -/
theorem groupProductInl_fst : groupProductInl G H ≫ groupProductFst G H = 𝟙 G := by
  ext x
  rfl

/-- The first inclusion is killed by the second projection. -/
theorem groupProductInl_snd : groupProductInl G H ≫ groupProductSnd G H = (1 : G ⟶ H) := by
  ext x
  rfl

/-- The second inclusion is killed by the first projection. -/
theorem groupProductInr_fst : groupProductInr G H ≫ groupProductFst G H = (1 : H ⟶ G) := by
  ext x
  rfl

/-- The second inclusion is a section of the second projection. -/
theorem groupProductInr_snd : groupProductInr G H ≫ groupProductSnd G H = 𝟙 H := by
  ext x
  rfl

/-- The first inclusion is the unique group morphism `G ⟶ G × H` with components `𝟙 G` and the
trivial homomorphism: the universal property of the product at the pair `(𝟙, 1)`. -/
theorem eq_groupProductInl (f : G ⟶ groupProduct G H)
    (h₁ : f ≫ groupProductFst G H = 𝟙 G)
    (h₂ : f ≫ groupProductSnd G H = (1 : G ⟶ H)) :
    f = groupProductInl G H := by
  apply BinaryFan.IsLimit.hom_ext (groupProductIsLimit G H)
  · change f ≫ groupProductFst G H = groupProductInl G H ≫ groupProductFst G H
    rw [h₁, groupProductInl_fst]
  · change f ≫ groupProductSnd G H = groupProductInl G H ≫ groupProductSnd G H
    rw [h₂, groupProductInl_snd]

/-- The second inclusion is the unique group morphism `H ⟶ G × H` whose two components are the
trivial homomorphism and `𝟙 H`. -/
theorem eq_groupProductInr (f : H ⟶ groupProduct G H)
    (h₁ : f ≫ groupProductFst G H = (1 : H ⟶ G))
    (h₂ : f ≫ groupProductSnd G H = 𝟙 H) :
    f = groupProductInr G H := by
  apply BinaryFan.IsLimit.hom_ext (groupProductIsLimit G H)
  · change f ≫ groupProductFst G H = groupProductInr G H ≫ groupProductFst G H
    rw [h₁, groupProductInr_fst]
  · change f ≫ groupProductSnd G H = groupProductInr G H ≫ groupProductSnd G H
    rw [h₂, groupProductInr_snd]

/-- The concrete product `G × H` is the binary product `Limits.prod G H` that Mathlib's
`GrpCat.hasLimits` chooses. -/
noncomputable def groupProductIsoProd : groupProduct G H ≅ Limits.prod G H :=
  (groupProductIsLimit G H).conePointUniqueUpToIso (limit.isLimit (pair G H))

end LeanCategories.Algebra
