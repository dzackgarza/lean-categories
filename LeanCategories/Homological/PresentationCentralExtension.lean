/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.FreeGroupPresentation
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The central extension attached to a free presentation

Weibel, *An Introduction to Homological Algebra* (1994), Construction 6.9.3,
pp. 199--200 (FC05-C06-U110).

For a free presentation `1 → R → F → G → 1`, Weibel quotients by the
relative commutator subgroup `[R,F]` and obtains

`1 → R/[R,F] → F/[R,F] → G → 1`.

The source then assumes that `G` is perfect and studies the restriction to
`[F,F]/[R,F]`; its surjectivity, kernel computation, perfection, and
universality are result-level statements.  This file closes only the
construction layer needed before those results.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

universe u v

namespace FreeGroupPresentation

variable {G : Type u} [Group G] (P : FreeGroupPresentation.{u, v} G)

/-- Weibel's relative commutator subgroup `[R,F]` for a free presentation. -/
def relationCommutator : Subgroup (FreeGroup P.Generators) :=
  ⁅P.relations, (⊤ : Subgroup (FreeGroup P.Generators))⁆

instance relationsNormal : P.relations.Normal := by
  dsimp [relations]
  infer_instance

instance relationCommutatorNormal : P.relationCommutator.Normal := by
  dsimp [relationCommutator]
  infer_instance

/-- The middle group `F/[R,F]` of Weibel's central extension. -/
abbrev centralCover :=
  FreeGroup P.Generators ⧸ P.relationCommutator

/-- The quotient map `F/[R,F] → G` induced by the presentation. -/
def centralCoverProjection : P.centralCover →* G :=
  QuotientGroup.lift P.relationCommutator P.quotientMap <|
    (Subgroup.commutator_le_left P.relations
      (⊤ : Subgroup (FreeGroup P.Generators))).trans_eq rfl

lemma centralCoverProjection_surjective :
    Function.Surjective P.centralCoverProjection :=
  QuotientGroup.lift_surjective_of_surjective
    P.relationCommutator P.quotientMap P.quotientMap_surjective
      ((Subgroup.commutator_le_left P.relations
        (⊤ : Subgroup (FreeGroup P.Generators))).trans_eq rfl)

/-- The image of `R` in `F/[R,F]`, i.e. the source model for
`R/[R,F]`. -/
def relationQuotientImage : Subgroup P.centralCover :=
  P.relations.map (QuotientGroup.mk' P.relationCommutator)

/-- The kernel of `F/[R,F] → G` is the image of `R`. -/
lemma centralCoverProjection_ker :
    P.centralCoverProjection.ker = P.relationQuotientImage := by
  exact QuotientGroup.ker_lift _ _ _

/-- The short exact group extension underlying Construction 6.9.3.  Its
kernel is represented as the actual kernel subgroup; the preceding lemma
identifies that subgroup with `R/[R,F]`. -/
def centralExtension :
    GroupExtension P.centralCoverProjection.ker P.centralCover G where
  inl := P.centralCoverProjection.ker.subtype
  rightHom := P.centralCoverProjection
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := by
    exact P.centralCoverProjection.ker.range_subtype
  rightHom_surjective := P.centralCoverProjection_surjective

/-- Definition-layer realization of the fact that the presentation quotient is
a *central* extension.  The quotient group and all maps are fixed above; the
only supplied datum is the source centrality verification. -/
structure CentralExtensionRealization : Prop where
  isCentral : P.centralCoverProjection.ker ≤ Subgroup.center P.centralCover

end FreeGroupPresentation

end LeanCategories.Homological
