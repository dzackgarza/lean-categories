/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Whiskering

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.CategoryTheory
universe v u v' u'
variable {D : Type u'} [Category.{v'} D]
variable {C : Type u} [Category.{v} C]

/-- The unit of the codensity monad induced by a self-right-Kan extension. -/
noncomputable def codensityUnit (G : D ⥤ C) (T : C ⥤ C) (ε : G ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] : 𝟭 C ⟶ T :=
  T.liftOfIsRightKanExtension ε (𝟭 C) (Functor.rightUnitor G).hom

/-- The multiplication of the codensity monad induced by a self-right-Kan extension. -/
noncomputable def codensityMult (G : D ⥤ C) (T : C ⥤ C) (ε : G ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] : T ⋙ T ⟶ T :=
  T.liftOfIsRightKanExtension ε (T ⋙ T)
    ((Functor.associator G T T).inv ≫ Functor.whiskerRight ε T ≫ ε)

lemma codensityUnit_fac_app (G : D ⥤ C) (T : C ⥤ C) (ε : G ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] (d : D) :
    (codensityUnit G T ε).app (G.obj d) ≫ ε.app d = 𝟙 (G.obj d) := by
  simp [codensityUnit]

lemma codensityMult_fac_app (G : D ⥤ C) (T : C ⥤ C) (ε : G ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] (d : D) :
    (codensityMult G T ε).app (G.obj d) ≫ ε.app d = T.map (ε.app d) ≫ ε.app d := by
  simp [codensityMult]

lemma codensityAssoc_nat (G : D ⥤ C) (T : C ⥤ C) (ε : G ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] :
    Functor.whiskerRight (codensityMult G T ε) T ≫ codensityMult G T ε =
      Functor.whiskerLeft T (codensityMult G T ε) ≫ codensityMult G T ε := by
  apply T.hom_ext_of_isRightKanExtension ε
  ext d
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  change
    (T.map ((codensityMult G T ε).app (G.obj d)) ≫
        (codensityMult G T ε).app (G.obj d)) ≫ ε.app d =
      ((codensityMult G T ε).app (T.obj (G.obj d)) ≫
        (codensityMult G T ε).app (G.obj d)) ≫ ε.app d
  calc
    (T.map ((codensityMult G T ε).app (G.obj d)) ≫ (codensityMult G T ε).app (G.obj d)) ≫ ε.app d =
        T.map ((codensityMult G T ε).app (G.obj d)) ≫
          ((codensityMult G T ε).app (G.obj d) ≫ ε.app d) := by rw [Category.assoc]
    _ = T.map ((codensityMult G T ε).app (G.obj d)) ≫ (T.map (ε.app d) ≫ ε.app d) := by
          rw [codensityMult_fac_app]
    _ = (T.map ((codensityMult G T ε).app (G.obj d)) ≫ T.map (ε.app d)) ≫ ε.app d := by
          rw [Category.assoc]
    _ = T.map ((codensityMult G T ε).app (G.obj d) ≫ ε.app d) ≫ ε.app d := by
          rw [T.map_comp]
    _ = T.map (T.map (ε.app d) ≫ ε.app d) ≫ ε.app d := by
          rw [codensityMult_fac_app]
    _ = (T.map (T.map (ε.app d)) ≫ T.map (ε.app d)) ≫ ε.app d := by
          rw [T.map_comp]
    _ = T.map (T.map (ε.app d)) ≫ (T.map (ε.app d) ≫ ε.app d) := by rw [Category.assoc]
    _ = T.map (T.map (ε.app d)) ≫ ((codensityMult G T ε).app (G.obj d) ≫ ε.app d) := by
          rw [codensityMult_fac_app]
    _ = (T.map (T.map (ε.app d)) ≫ (codensityMult G T ε).app (G.obj d)) ≫ ε.app d := by
          rw [Category.assoc]
    _ = ((codensityMult G T ε).app (T.obj (G.obj d)) ≫ T.map (ε.app d)) ≫ ε.app d := by
          have h := (codensityMult G T ε).naturality (ε.app d)
          simp only [Functor.comp_map] at h
          exact congrArg (fun q => q ≫ ε.app d) h
    _ = (codensityMult G T ε).app (T.obj (G.obj d)) ≫ (T.map (ε.app d) ≫ ε.app d) := by
          rw [Category.assoc]
    _ = (codensityMult G T ε).app (T.obj (G.obj d)) ≫
          ((codensityMult G T ε).app (G.obj d) ≫ ε.app d) := by rw [codensityMult_fac_app]
    _ = ((codensityMult G T ε).app (T.obj (G.obj d)) ≫
          (codensityMult G T ε).app (G.obj d)) ≫ ε.app d := by
          rw [Category.assoc]

lemma codensityLeftUnit_nat (G : D ⥤ C) (T : C ⥤ C) (ε : G ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] :
    Functor.whiskerLeft T (codensityUnit G T ε) ≫ codensityMult G T ε = 𝟙 T := by
  apply T.hom_ext_of_isRightKanExtension ε
  ext d
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  change
    ((codensityUnit G T ε).app (T.obj (G.obj d)) ≫
        (codensityMult G T ε).app (G.obj d)) ≫ ε.app d =
      NatTrans.app (𝟙 T) (G.obj d) ≫ ε.app d
  calc
    ((codensityUnit G T ε).app (T.obj (G.obj d)) ≫ (codensityMult G T ε).app (G.obj d)) ≫ ε.app d =
        (codensityUnit G T ε).app (T.obj (G.obj d)) ≫
          ((codensityMult G T ε).app (G.obj d) ≫ ε.app d) := by rw [Category.assoc]
    _ = (codensityUnit G T ε).app (T.obj (G.obj d)) ≫ (T.map (ε.app d) ≫ ε.app d) := by
          rw [codensityMult_fac_app]
    _ = ((codensityUnit G T ε).app (T.obj (G.obj d)) ≫ T.map (ε.app d)) ≫ ε.app d := by
          rw [Category.assoc]
    _ = (ε.app d ≫ (codensityUnit G T ε).app (G.obj d)) ≫ ε.app d := by
          have h := (codensityUnit G T ε).naturality (ε.app d)
          simp only [Functor.id_map, Functor.comp_obj] at h
          exact congrArg (fun q => q ≫ ε.app d) h.symm
    _ = ε.app d ≫ ((codensityUnit G T ε).app (G.obj d) ≫ ε.app d) := by rw [Category.assoc]
    _ = ε.app d := by rw [codensityUnit_fac_app, Category.comp_id]
    _ = NatTrans.app (𝟙 T) (G.obj d) ≫ ε.app d := by simp [NatTrans.id_app]

lemma codensityRightUnit_nat (G : D ⥤ C) (T : C ⥤ C) (ε : G ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] :
    Functor.whiskerRight (codensityUnit G T ε) T ≫ codensityMult G T ε = 𝟙 T := by
  apply T.hom_ext_of_isRightKanExtension ε
  ext d
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  change
    (T.map ((codensityUnit G T ε).app (G.obj d)) ≫
        (codensityMult G T ε).app (G.obj d)) ≫ ε.app d =
      NatTrans.app (𝟙 T) (G.obj d) ≫ ε.app d
  calc
    (T.map ((codensityUnit G T ε).app (G.obj d)) ≫ (codensityMult G T ε).app (G.obj d)) ≫ ε.app d =
        T.map ((codensityUnit G T ε).app (G.obj d)) ≫
          ((codensityMult G T ε).app (G.obj d) ≫ ε.app d) := by rw [Category.assoc]
    _ = T.map ((codensityUnit G T ε).app (G.obj d)) ≫ (T.map (ε.app d) ≫ ε.app d) := by
          rw [codensityMult_fac_app]
    _ = (T.map ((codensityUnit G T ε).app (G.obj d)) ≫ T.map (ε.app d)) ≫ ε.app d := by
          rw [Category.assoc]
    _ = T.map ((codensityUnit G T ε).app (G.obj d) ≫ ε.app d) ≫ ε.app d := by
          rw [T.map_comp]
    _ = T.map (𝟙 (G.obj d)) ≫ ε.app d := by rw [codensityUnit_fac_app]
    _ = ε.app d := by simp
    _ = NatTrans.app (𝟙 T) (G.obj d) ≫ ε.app d := by simp [NatTrans.id_app]

/-- Riehl Definition 6.5.10 (FC03-C06-U046): if `T` is the right Kan extension of
`G : D ⥤ C` along itself, the resulting endofunctor carries its canonical codensity monad
structure. -/
noncomputable def codensityMonad (G : D ⥤ C) (T : C ⥤ C) (ε : G ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] : Monad C where
  toFunctor := T
  η := codensityUnit G T ε
  μ := codensityMult G T ε
  assoc X := NatTrans.congr_app (codensityAssoc_nat G T ε) X
  left_unit X := NatTrans.congr_app (codensityLeftUnit_nat G T ε) X
  right_unit X := NatTrans.congr_app (codensityRightUnit_nat G T ε) X

end LeanCategories.CategoryTheory
