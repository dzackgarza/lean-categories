/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.TopCat.Path
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace LeanCategories.Topology
universe u

noncomputable def point0 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u} :=
  TopCat.ofHom (ContinuousMap.const _ (0 : TopCat.I))
noncomputable def point1 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u} :=
  TopCat.ofHom (ContinuousMap.const _ (1 : TopCat.I))

noncomputable def leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u} :=
  TopCat.ofHom
    { toFun := fun x => TopCat.I.homeomorph.symm ⟨(TopCat.I.homeomorph x : ℝ) / 2, by
        constructor
        · have hx := (TopCat.I.homeomorph x).2.1; linarith
        · have hx := (TopCat.I.homeomorph x).2.2; linarith⟩
      continuous_toFun := by fun_prop }

noncomputable def rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u} :=
  TopCat.ofHom
    { toFun := fun x => TopCat.I.homeomorph.symm ⟨((TopCat.I.homeomorph x : ℝ) + 1) / 2, by
        constructor
        · have hx := (TopCat.I.homeomorph x).2.1; linarith
        · have hx := (TopCat.I.homeomorph x).2.2; linarith⟩
      continuous_toFun := by fun_prop }

@[simp] lemma leftHalf_apply (x : TopCat.I.{u}) :
    TopCat.I.homeomorph (leftHalf x) = ⟨(TopCat.I.homeomorph x : ℝ) / 2, by
      constructor
      · have hx := (TopCat.I.homeomorph x).2.1; linarith
      · have hx := (TopCat.I.homeomorph x).2.2; linarith⟩ := rfl
@[simp] lemma rightHalf_apply (x : TopCat.I.{u}) :
    TopCat.I.homeomorph (rightHalf x) = ⟨((TopCat.I.homeomorph x : ℝ) + 1) / 2, by
      constructor
      · have hx := (TopCat.I.homeomorph x).2.1; linarith
      · have hx := (TopCat.I.homeomorph x).2.2; linarith⟩ := rfl

lemma glue_condition :
    (point1 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u}) ≫
        (leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) =
      (point0 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u}) ≫
        (rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) := by
  ext x
  cases x
  change (1 : ℝ) / 2 = (0 + 1 : ℝ) / 2
  norm_num

noncomputable def intervalPushoutCocone :
    PushoutCocone
      (point1 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u})
      (point0 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u}) :=
  PushoutCocone.mk
    (leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u})
    (rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u})
    glue_condition

noncomputable def concat {X : TopCat.{u}} (f g : TopCat.I.{u} ⟶ X)
    (h : f 1 = g 0) : TopCat.I.{u} ⟶ X := by
  let p : X.Path (f 0) (f 1) := { hom := f, hom₀ := rfl, hom₁ := rfl }
  let q : X.Path (f 1) (g 1) := { hom := g, hom₀ := h.symm, hom₁ := rfl }
  exact (TopCat.pathEquiv.symm ((TopCat.pathEquiv p).trans (TopCat.pathEquiv q))).hom

end LeanCategories.Topology

namespace LeanCategories.Topology

lemma cocone_endpoint (s : PushoutCocone
    (point1 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u})
    (point0 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u})) : s.inl 1 = s.inr 0 := by
  have h := ConcreteCategory.congr_hom s.condition PUnit.unit
  rw [TopCat.comp_app, TopCat.comp_app] at h
  change s.inl 1 = s.inr 0 at h
  exact h

lemma concat_apply {X : TopCat.{u}} (f g : TopCat.I.{u} ⟶ X)
    (h : f 1 = g 0) (t : TopCat.I.{u}) :
    concat f g h t =
      ((TopCat.pathEquiv
        ({ hom := f, hom₀ := rfl, hom₁ := rfl } : X.Path (f 0) (f 1))).trans
       (TopCat.pathEquiv
        ({ hom := g, hom₀ := h.symm, hom₁ := rfl } : X.Path (f 1) (g 1))))
        (TopCat.I.homeomorph t) := by
  rfl

lemma concat_left {X : TopCat.{u}} (f g : TopCat.I.{u} ⟶ X)
    (h : f 1 = g 0) :
    (leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) ≫ concat f g h = f := by
  ext x
  rw [TopCat.comp_app, concat_apply, Path.trans_apply]
  split_ifs with hx
  · change f (TopCat.I.homeomorph.symm
      ⟨2 * (TopCat.I.homeomorph ((leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) x) : ℝ), _⟩) = f x
    apply congrArg f
    apply TopCat.I.ext
    ext
    change 2 * ((TopCat.I.homeomorph x : ℝ) / 2) = (TopCat.I.homeomorph x : ℝ)
    ring
  · exfalso
    have hc : (TopCat.I.homeomorph ((leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) x) : ℝ) =
        (TopCat.I.homeomorph x : ℝ) / 2 := by rfl
    rw [hc] at hx
    have hx1 := (TopCat.I.homeomorph x).2.2
    exact hx (by linarith)

lemma concat_right {X : TopCat.{u}} (f g : TopCat.I.{u} ⟶ X)
    (h : f 1 = g 0) :
    (rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) ≫ concat f g h = g := by
  ext x
  rw [TopCat.comp_app, concat_apply, Path.trans_apply]
  split_ifs with hx
  · have hc : (TopCat.I.homeomorph ((rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) x) : ℝ) =
        ((TopCat.I.homeomorph x : ℝ) + 1) / 2 := by rfl
    have hx0 := (TopCat.I.homeomorph x).2.1
    have heq : (TopCat.I.homeomorph x : ℝ) = 0 := by
      rw [hc] at hx
      linarith
    have hx' : x = 0 := by
      apply TopCat.I.ext
      ext
      simp [heq]
    subst x
    change f (TopCat.I.homeomorph.symm
      ⟨2 * (TopCat.I.homeomorph ((rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) 0) : ℝ), _⟩) = g 0
    rw [← h]
    apply congrArg f
    apply TopCat.I.ext
    ext
    change 2 * ((0 + 1 : ℝ) / 2) = 1
    norm_num
  · change g (TopCat.I.homeomorph.symm
      ⟨2 * (TopCat.I.homeomorph ((rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) x) : ℝ) - 1, _⟩) = g x
    apply congrArg g
    apply TopCat.I.ext
    ext
    change 2 * (((TopCat.I.homeomorph x : ℝ) + 1) / 2) - 1 = (TopCat.I.homeomorph x : ℝ)
    ring

end LeanCategories.Topology

namespace LeanCategories.Topology



/-- FC03-CE-U004: the two half-interval inclusions exhibit the unit interval as the pushout
of two copies of the unit interval obtained by identifying the right endpoint of the first with
the left endpoint of the second. -/
noncomputable def intervalPushoutIsColimit : IsColimit (intervalPushoutCocone : PushoutCocone
    (point1 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u})
    (point0 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u})) :=
  PushoutCocone.IsColimit.mk glue_condition
    (fun s => concat s.inl s.inr (cocone_endpoint s))
    (fun s => concat_left s.inl s.inr (cocone_endpoint s))
    (fun s => concat_right s.inl s.inr (cocone_endpoint s))
    (fun s m hmL hmR => by
      ext t
      by_cases ht : (TopCat.I.homeomorph t : ℝ) ≤ 1 / 2
      · let x : TopCat.I.{u} := TopCat.I.homeomorph.symm
          ⟨2 * (TopCat.I.homeomorph t : ℝ), by
            constructor
            · have h0 := (TopCat.I.homeomorph t).2.1
              linarith
            · linarith⟩
        have hx : (leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) x = t := by
          apply TopCat.I.ext
          ext
          change (2 * (TopCat.I.homeomorph t : ℝ)) / 2 = (TopCat.I.homeomorph t : ℝ)
          ring
        have hcomp :
            (leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) ≫ m =
              (leftHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) ≫
                concat s.inl s.inr (cocone_endpoint s) :=
          hmL.trans (concat_left s.inl s.inr (cocone_endpoint s)).symm
        have hpt := ConcreteCategory.congr_hom hcomp x
        rw [TopCat.comp_app, TopCat.comp_app] at hpt
        simpa [hx] using hpt
      · let x : TopCat.I.{u} := TopCat.I.homeomorph.symm
          ⟨2 * (TopCat.I.homeomorph t : ℝ) - 1, by
            constructor
            · have hgt : 1 / 2 < (TopCat.I.homeomorph t : ℝ) := lt_of_not_ge ht
              linarith
            · have h1 := (TopCat.I.homeomorph t).2.2
              linarith⟩
        have hx : (rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) x = t := by
          apply TopCat.I.ext
          ext
          change ((2 * (TopCat.I.homeomorph t : ℝ) - 1) + 1) / 2 =
            (TopCat.I.homeomorph t : ℝ)
          ring
        have hcomp :
            (rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) ≫ m =
              (rightHalf : TopCat.I.{u} ⟶ TopCat.I.{u}) ≫
                concat s.inl s.inr (cocone_endpoint s) :=
          hmR.trans (concat_right s.inl s.inr (cocone_endpoint s)).symm
        have hpt := ConcreteCategory.congr_hom hcomp x
        rw [TopCat.comp_app, TopCat.comp_app] at hpt
        simpa only [hx] using hpt)

/-- The explicit categorical homeomorphism `I ≅ I ∨ I` from FC03-CE-U004, where the wedge is
Mathlib's chosen pushout of the endpoint maps `1 : * ⟶ I` and `0 : * ⟶ I`.  An isomorphism in
`TopCat` is precisely a homeomorphism of the underlying spaces. -/
noncomputable def intervalWedgeIso :
    TopCat.I.{u} ≅ pushout
      (point1 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u})
      (point0 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u}) :=
  intervalPushoutIsColimit.coconePointUniqueUpToIso
    (colimit.isColimit (span
      (point1 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u})
      (point0 : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u})))

end LeanCategories.Topology
