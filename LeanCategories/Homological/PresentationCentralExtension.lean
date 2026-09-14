/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.FreeGroupPresentation
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.IsPerfect
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

@[simp]
lemma centralCoverProjection_mk (f : FreeGroup P.Generators) :
    P.centralCoverProjection (QuotientGroup.mk' P.relationCommutator f) =
      P.quotientMap f := by
  unfold centralCoverProjection
  apply QuotientGroup.lift_mk'

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

/-- The image of `R` in `F/[R,F]` is central: the quotient map kills exactly
the relative commutator subgroup `[R,F]`, so every image of a relation commutes
with every element of the quotient. -/
lemma relationQuotientImage_le_center :
    P.relationQuotientImage ≤ Subgroup.center P.centralCover := by
  rw [← Subgroup.commutator_top_right_eq_bot_iff_le_center]
  let q : FreeGroup P.Generators →* P.centralCover :=
    QuotientGroup.mk' P.relationCommutator
  have htop : (⊤ : Subgroup (FreeGroup P.Generators)).map q = ⊤ :=
    Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective P.relationCommutator)
  change ⁅P.relations.map q, (⊤ : Subgroup P.centralCover)⁆ = ⊥
  rw [← htop, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
  change P.relationCommutator ≤ q.ker
  rw [QuotientGroup.ker_mk']

/-- Hence the constructed group extension is central. -/
lemma centralCoverProjection_ker_le_center :
    P.centralCoverProjection.ker ≤ Subgroup.center P.centralCover := by
  rw [P.centralCoverProjection_ker]
  exact P.relationQuotientImage_le_center

/-- The source model for `[F,F]/[R,F]`: the image of the commutator subgroup
of the free group inside `F/[R,F]`. -/
def perfectCover : Subgroup P.centralCover :=
  (_root_.commutator (FreeGroup P.Generators)).map
    (QuotientGroup.mk' P.relationCommutator)

/-- Restriction of `F/[R,F] → G` to `[F,F]/[R,F]`. -/
def perfectCoverProjection : P.perfectCover →* G :=
  P.centralCoverProjection.domRestrict P.perfectCover

/-- If `G` is perfect, the restricted map `[F,F]/[R,F] → G` is surjective. -/
lemma perfectCoverProjection_surjective [Group.IsPerfect G] :
    Function.Surjective P.perfectCoverProjection := by
  let F := FreeGroup P.Generators
  let π := P.quotientMap
  let q : F →* P.centralCover := QuotientGroup.mk' P.relationCommutator
  have hmap : (_root_.commutator F).map π = _root_.commutator G := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π P.quotientMap_surjective,
      _root_.commutator_def]
  intro g
  have hg : g ∈ _root_.commutator G := Group.IsPerfect.mem_commutator
  rw [← hmap] at hg
  obtain ⟨f, hf, hfg⟩ := hg
  let x : P.perfectCover := ⟨q f, ⟨f, hf, rfl⟩⟩
  refine ⟨x, ?_⟩
  change P.centralCoverProjection (q f) = g
  rw [show q f = QuotientGroup.mk' P.relationCommutator f from rfl,
    P.centralCoverProjection_mk]
  exact hfg

/-- The subgroup of the free group whose quotient is the kernel of the
perfect-cover restriction: `R ∩ [F,F]`. -/
def perfectKernelPreimage : Subgroup (FreeGroup P.Generators) :=
  P.relations ⊓ _root_.commutator (FreeGroup P.Generators)

/-- The image of `R ∩ [F,F]` in `F/[R,F]`. -/
def perfectKernelImage : Subgroup P.centralCover :=
  P.perfectKernelPreimage.map (QuotientGroup.mk' P.relationCommutator)

lemma perfectKernelImage_le_perfectCover :
    P.perfectKernelImage ≤ P.perfectCover := by
  exact Subgroup.map_mono inf_le_right

/-- The kernel of `[F,F]/[R,F] → G`, viewed back in `F/[R,F]`, is exactly
the image of `R ∩ [F,F]`.  This is the source kernel
`(R ∩ [F,F])/[R,F]`. -/
lemma perfectCoverProjection_kernel_image :
    P.perfectCoverProjection.ker.map P.perfectCover.subtype = P.perfectKernelImage := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases y with ⟨y, hyC⟩
    change P.centralCoverProjection y = 1 at hy
    have hyker : y ∈ P.centralCoverProjection.ker := MonoidHom.mem_ker.mpr hy
    rw [P.centralCoverProjection_ker] at hyker
    rcases hyker with ⟨r, hrR, hry⟩
    rcases hyC with ⟨c, hcC, hcy⟩
    have hqrc : QuotientGroup.mk' P.relationCommutator r =
        QuotientGroup.mk' P.relationCommutator c := by
      exact hry.trans hcy.symm
    have hrc : r * c⁻¹ ∈ P.relationCommutator := by
      have hrc' : r / c ∈ P.relationCommutator :=
        QuotientGroup.eq_iff_div_mem.mp (by simpa using hqrc)
      simpa [div_eq_mul_inv] using hrc'
    have hN_R : P.relationCommutator ≤ P.relations :=
      Subgroup.commutator_le_left _ _
    have hN_C : P.relationCommutator ≤ _root_.commutator (FreeGroup P.Generators) := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_rfl
    have hcR : c ∈ P.relations := by
      have : r * c⁻¹ ∈ P.relations := hN_R hrc
      have hcinv : c⁻¹ ∈ P.relations :=
        (P.relations.mul_mem_cancel_left hrR).mp this
      simpa using P.relations.inv_mem hcinv
    refine ⟨c, ⟨hcR, hcC⟩, ?_⟩
    exact hcy
  · rintro ⟨f, ⟨hfR, hfC⟩, rfl⟩
    let q : FreeGroup P.Generators →* P.centralCover :=
      QuotientGroup.mk' P.relationCommutator
    let y : P.perfectCover := ⟨q f, ⟨f, hfC, rfl⟩⟩
    refine ⟨y, ?_, rfl⟩
    change P.centralCoverProjection (q f) = 1
    rw [show q f = QuotientGroup.mk' P.relationCommutator f from rfl,
      P.centralCoverProjection_mk]
    exact MonoidHom.mem_ker.mp hfR

end FreeGroupPresentation

end LeanCategories.Homological
