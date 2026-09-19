/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import LeanCategories.ForMathlib.SimplexCategoryGeneratorsRelationsEquivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

@[expose] public section
/-! # Simplicial objects by generators and relations

This file provides the basic API for leveraging the equivalence obtained in
`Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Equivalence`. This is
the intended way of using this equivalence.

## Main results
  - `CosimplicialObject.ofGeneratorsAndRelations` constructs a cosimplicial objects
  out of the data of objects `n ↦ X n` as well as codegeneracies `σ i : X (n + 1) → X n`
  and cofaces `δ i : X n ⟶ X (n + 1)`, as long as they satisfy the simplicial identities.
  - The value at `mk n` of `CosimplicialObject.ofGeneratorsAndRelations` has a canonical
  isomorphism `CosimplicialObject.ofGeneratorsAndRelationsObjMkIso` with the provided object `X n`.
  - Up to conjugation by this isomorphism, the cofaces and codegeneracies maps are ones we started
  with.
  - `CosimplicialObject.mkNatTrans` (resp. `CosimplicialObject.mkNatIso`) builds a natural
  transformation (resp isomorphism) of cosimplicial objects `X Y` out of the data of maps
  `X _[n] ⟶ Y _[n]` that commutes with cofaces and codegeneracies.
  - Dual results for simplicial objects are provided.

-/

namespace CategoryTheory

open CategoryTheory SimplexCategory

namespace CosimplicialObject

variable {C : Type*} [Category C]

section MkCosimplicialObject

variable (X : ℕ → C)
  (σ : ∀ {n : ℕ} (_ : Fin (n + 1)), X (n + 1) ⟶ X n)
  (δ : ∀ {n : ℕ} (_ : Fin (n + 2)), X n ⟶ X (n + 1))
  (s1: ∀ {n : ℕ} (i j : Fin (n + 2)) (_ : i ≤ j), δ i ≫ δ j.succ = δ j ≫ δ i.castSucc)
  (s2: ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (_ : i ≤ j.castSucc),
    δ i.castSucc ≫ σ j.succ = σ j ≫ δ i)
  (s3₁: ∀ {n : ℕ} (i : Fin (n + 1)), δ i.castSucc ≫ σ i = 𝟙 (X n))
  (s3₂: ∀ {n : ℕ} (i : Fin (n + 1)), δ i.succ ≫ σ i = 𝟙 (X n))
  (s4: ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (_ : j.castSucc < i),
      δ i.succ ≫ σ j.castSucc = σ j ≫ δ i)
  (s5: ∀ {n : ℕ} (i j : Fin (n + 1)) (_ : i ≤ j),
      σ i.castSucc ≫ σ j = σ j.succ ≫ σ i)

/-- Making a cosimplicial object out of generators and relations. -/
set_option backward.isDefEq.respectTransparency false in
noncomputable def ofGeneratorsAndRelations: CosimplicialObject C :=
  SimplexCategoryGenRel.equivSimplexCategory.inverse ⋙ (
    CategoryTheory.Quotient.lift FreeSimplexQuiver.homRel
      (Paths.lift {
        obj x := X x.len
        map {x y} f := match f with
          | .σ i => σ i
          | .δ i => δ i})
      (by
        intro x y f g hfg
        cases hfg with
        | δ_comp_δ H =>
          simp only [Paths.of_obj, Paths.of_map, Functor.map_comp,
            Paths.lift_toPath]
          exact s1 _ _ H
        | δ_comp_σ_of_le H =>
          simp only [Paths.of_obj, Paths.of_map, Functor.map_comp,
            Paths.lift_toPath]
          exact s2 _ _ H
        | δ_comp_σ_self =>
          simp only [Paths.of_obj, Paths.of_map, Functor.map_comp,
            Paths.lift_toPath]
          exact s3₁ _
        | δ_comp_σ_succ =>
          simp only [Paths.of_obj, Paths.of_map, Functor.map_comp,
            Paths.lift_toPath]
          exact s3₂ _
        | δ_comp_σ_of_gt H =>
          simp only [Paths.of_obj, Paths.of_map, Functor.map_comp,
            Paths.lift_toPath]
          exact s4 _ _ H
        | σ_comp_σ H =>
          simp only [Paths.of_obj, Paths.of_map, Functor.map_comp,
            Paths.lift_toPath]
          exact s5 _ _ H ))

open SimplexCategoryGenRel in
/-- The cosimplicial object defined by generators and relations has the expected value on objects
up to isomorphism. -/
noncomputable def ofGeneratorsAndRelationsObjMkIso (n : ℕ) :
    (ofGeneratorsAndRelations X σ δ s1 s2 s3₁ s3₂ s4 s5).obj (.mk n) ≅ X n := by
  dsimp only [ofGeneratorsAndRelations, Functor.comp_obj]
  exact ((_ : SimplexCategoryGenRel ⥤ C).mapIso (equivSimplexCategory_inverse_objIsoMk n)).trans
    (Iso.refl _)

/-- Up to the same isomorphisms, a cosimplicial object defined by generators and relations
has the provided functoriality maps for `σ`. -/
@[reassoc (attr := simp)]
lemma ofGeneratorsAndRelations_map_σ {n : ℕ} (i : Fin (n + 1)) :
    (ofGeneratorsAndRelationsObjMkIso X σ δ s1 s2 s3₁ s3₂ s4 s5 (n + 1)).inv ≫
      (ofGeneratorsAndRelations X σ δ s1 s2 s3₁ s3₂ s4 s5).σ i ≫
        (ofGeneratorsAndRelationsObjMkIso X σ δ s1 s2 s3₁ s3₂ s4 s5 n).hom
        = σ i := by
  simp [CosimplicialObject.σ, ofGeneratorsAndRelations, ofGeneratorsAndRelationsObjMkIso,
    ← Functor.map_comp, Quotient.lift_map_functor_map]

/-- Up to the same isomorphisms, a cosimplicial object defined by generators and relations
has the provided functoriality maps for `δ`. -/
@[reassoc (attr := simp)]
lemma ofGeneratorsAndRelations_map_δ {n : ℕ} (i : Fin (n + 2)) :
    (ofGeneratorsAndRelationsObjMkIso X σ δ s1 s2 s3₁ s3₂ s4 s5 n).inv ≫
      (ofGeneratorsAndRelations X σ δ s1 s2 s3₁ s3₂ s4 s5).δ i ≫
        (ofGeneratorsAndRelationsObjMkIso X σ δ s1 s2 s3₁ s3₂ s4 s5 (n + 1)).hom
        = δ i := by
  simp [CosimplicialObject.δ, ofGeneratorsAndRelations, ofGeneratorsAndRelationsObjMkIso,
    ← Functor.map_comp, Quotient.lift_map_functor_map]

end MkCosimplicialObject

section MkNatTrans

variable (X Y : CosimplicialObject C)
  (app : ∀ (Δ : SimplexCategory), X.obj Δ ⟶ Y.obj Δ)
  (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), X.δ i ≫ app (.mk (n + 1)) = app (.mk n) ≫ Y.δ i)
  (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), X.σ i ≫ app (.mk n) = app (.mk (n + 1)) ≫ Y.σ i)

open SimplexCategoryGenRel in
/-- Construct a natural transformation between cosimplicial objects out of an application that
commutes with cofaces and codegeneracies. -/
set_option backward.isDefEq.respectTransparency false in
noncomputable def mkNatTrans: X ⟶ Y :=
    letI : equivSimplexCategory.functor ⋙ X ⟶ equivSimplexCategory.functor ⋙ Y :=
      Quotient.natTransLift _ {
        app n := app (.mk n)
        naturality {x y} f := by
          induction f using Paths.induction with
          | id => simp
          | @comp z t a f g h_rec =>
            simp only [Paths.of_obj, Functor.comp_obj, Paths.of_map, Functor.comp_map,
              Functor.map_comp, Category.assoc] at h_rec ⊢
            cases g with
            | @δ n i =>
              slice_rhs 1 2 => rw [← h_rec]
              rw [Category.assoc]
              congr 1
              exact hδ i
            | @σ n j =>
              slice_rhs 1 2 => rw [← h_rec]
              rw [Category.assoc]
              congr 1
              exact hσ j }
    (Functor.rightUnitor _).inv ≫ (Functor.whiskerRight equivSimplexCategory.counitInv X) ≫
      (Functor.associator _ _ _).hom ≫
        (Functor.whiskerLeft equivSimplexCategory.inverse this) ≫
        (Functor.associator _ _ _).inv ≫ (Functor.whiskerRight equivSimplexCategory.counit Y) ≫
          (Functor.rightUnitor _).hom

variable {hδ} {hσ}

open SimplexCategoryGenRel in
/-- The natural transformation built using `mkNatTrans` have the expected application. -/
@[simp]
lemma mkNatTrans_app (Δ : SimplexCategory) : (mkNatTrans X Y app hδ hσ).app Δ = app Δ := by
  dsimp [mkNatTrans]
  simp only [Category.comp_id, Category.id_comp]
  generalize_proofs p
  letI : equivSimplexCategory.functor ⋙ X ⟶ equivSimplexCategory.functor ⋙ Y :=
    Quotient.natTransLift _
      { app n := app (.mk n)
        naturality := p}
  have h_nat := this.naturality (equivSimplexCategory_inverse_objIsoMk Δ.len).hom
  simp only [Functor.comp_obj, equivSimplexCategory_functor_obj_mk,
    equivSimplexCategory_inverse_objIsoMk, Functor.id_obj, Iso.symm_hom, Iso.app_inv,
    Functor.comp_map] at h_nat
  have h :
      equivSimplexCategory.counit.app (.mk Δ.len) =
        equivSimplexCategory.functor.map (equivSimplexCategory.unitIso.inv.app (mk Δ.len)) := by
    rw [← equivSimplexCategory.counit_app_functor]
    rfl
  rw [←SimplexCategory.mk_len Δ, h, ← h_nat, ← Functor.map_comp_assoc]
  rw [← equivSimplexCategory.counit_app_functor]
  simp only [equivSimplexCategory_functor_obj_mk, Iso.inv_hom_id_app, Functor.id_obj,
    CategoryTheory.Functor.map_id, Category.id_comp, this]
  rfl

lemma mkNatTrans_comp X Y (Z : CosimplicialObject C) app
    (app' : ∀ (Δ : SimplexCategory), Y.obj Δ ⟶ Z.obj Δ)
    {hδ} {hσ}
    {hδ' : ∀ {n : ℕ} (i : Fin (n + 2)), Y.δ i ≫ app' (.mk (n + 1)) = app' (.mk n) ≫ Z.δ i}
    {hσ' : ∀ {n : ℕ} (i : Fin (n + 1)), Y.σ i ≫ app' (.mk n) = app' (.mk (n + 1)) ≫ Z.σ i}
    : mkNatTrans X Z (fun n ↦ app n ≫ app' n)
        (by intro n i; rw [reassoc_of%(hδ i), hδ' i]; simp)
        (by intro n i; rw [reassoc_of%(hσ i), hσ' i]; simp)
      = (mkNatTrans X Y app hδ hσ) ≫ (mkNatTrans Y Z app' hδ' hσ') := by
  ext Δ
  simp only [mkNatTrans_app, instCategoryCosimplicialObject_comp_app]
  rw [mkNatTrans_app] <;> assumption

@[simp]
lemma mkNatTrans_id :
  mkNatTrans X X (fun x ↦ 𝟙 _) (by simp) (by simp) = 𝟙 X := by
    ext x
    simp

end MkNatTrans

section MkNatIso

variable (X Y : CosimplicialObject C)
  (app : ∀ (Δ : SimplexCategory), X.obj Δ ≅ Y.obj Δ)
  (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), X.δ i ≫ (app (.mk (n + 1))).hom = (app (.mk n)).hom ≫ Y.δ i)
  (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), X.σ i ≫ (app (.mk n)).hom = (app (.mk (n + 1))).hom ≫ Y.σ i)

/-- Construct a natural isomorphism between cosimplicial objects out of an isomorphism that commutes
with cofaces and codegeneracies. -/
noncomputable def mkNatIso: X ≅ Y where
  hom := mkNatTrans X Y (fun x ↦ (app x).hom) hδ hσ
  inv := mkNatTrans Y X (fun x ↦ (app x).inv)
    (by intro n i
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
        exact (hδ i).symm)
    (by intro n i
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
        exact (hσ i).symm)

variable {hδ} {hσ}
@[simp]
lemma mkNatIso_hom_app (Δ : SimplexCategory) :
    (mkNatIso X Y app hδ hσ).hom.app Δ = (app Δ).hom := by simp [mkNatIso]

@[simp]
lemma mkNatIso_inv_app (Δ : SimplexCategory) :
    (mkNatIso X Y app hδ hσ).inv.app Δ = (app Δ).inv := by
  simp only [mkNatIso]
  generalize_proofs p p'
  rw [mkNatTrans_app] <;> assumption

end MkNatIso

end CosimplicialObject

namespace SimplicialObject

variable {C : Type*} [Category C]

section MkSimplicialObject

variable (X : ℕ → C)
  (σ : ∀ {n : ℕ} (_ : Fin (n + 1)), X n ⟶ X (n + 1))
  (δ : ∀ {n : ℕ} (_ : Fin (n + 2)), X (n + 1) ⟶ X n)
  (s1: ∀ {n : ℕ} (i j : Fin (n + 2)) (_ : i ≤ j), δ j.succ ≫ δ i = δ i.castSucc ≫ δ j)
  (s2: ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (_ : i ≤ j.castSucc),
    σ j.succ ≫ δ i.castSucc  = δ i ≫ σ j)
  (s3₁: ∀ {n : ℕ} (i : Fin (n + 1)), σ i ≫ δ i.castSucc = 𝟙 (X n))
  (s3₂: ∀ {n : ℕ} (i : Fin (n + 1)), σ i ≫ δ i.succ  = 𝟙 (X n))
  (s4: ∀ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (_ : j.castSucc < i),
    σ j.castSucc ≫ δ i.succ  = δ i ≫ σ j )
  (s5: ∀ {n : ℕ} (i j : Fin (n + 1)) (_ : i ≤ j),
      σ j ≫ σ i.castSucc = σ i ≫ σ j.succ )

/-- Making a simplicial object out of generators and relations. -/
noncomputable def ofGeneratorsAndRelations: SimplicialObject C :=
  Functor.leftOp <|
    CosimplicialObject.ofGeneratorsAndRelations
      (fun n ↦ Opposite.op (X n))
      (fun j ↦ (σ j).op)
      (fun j ↦ (δ j).op)
      (by intros; simp only [← op_comp]; congr 1; apply s1; assumption)
      (by intros; simp only [← op_comp]; congr 1; apply s2; assumption)
      (by intros; simp only [← op_comp]; congr 1; apply s3₁)
      (by intros; simp only [← op_comp]; congr 1; apply s3₂)
      (by intros; simp only [← op_comp]; congr 1; apply s4; assumption)
      (by intros; simp only [← op_comp]; congr 1; apply s5; assumption)

open SimplexCategoryGenRel in
/-- The simplicial object defined by generators and relations has the expected value on objects
up to isomorphism. -/
noncomputable def ofGeneratorsAndRelationsObjMkIso (n : ℕ) :
    X n ≅ (ofGeneratorsAndRelations X σ δ s1 s2 s3₁ s3₂ s4 s5).obj (Opposite.op (.mk n)) := by
  dsimp only [ofGeneratorsAndRelations, Functor.leftOp_obj]
  apply (isoOpEquiv _ _).toFun
  generalize_proofs p₁ p₂ p₃ p₄ p₅ p₆
  exact CosimplicialObject.ofGeneratorsAndRelationsObjMkIso
    (fun n ↦ Opposite.op (X n)) (fun j ↦ (σ j).op) (fun j ↦ (δ j).op) p₁ p₂ p₃ p₄ p₅ p₆ n

open SimplexCategoryGenRel in
/-- Up to the same isomorphisms, a simplicial object defined by generators and relations
has the provided functoriality maps for `σ`. -/
@[reassoc (attr := simp)]
lemma ofGeneratorsAndRelations_map_σ {n : ℕ} (i : Fin (n + 1)) :
    (ofGeneratorsAndRelationsObjMkIso X σ δ s1 s2 s3₁ s3₂ s4 s5 n).hom ≫
      (ofGeneratorsAndRelations X σ δ s1 s2 s3₁ s3₂ s4 s5).σ i ≫
        (ofGeneratorsAndRelationsObjMkIso X σ δ s1 s2 s3₁ s3₂ s4 s5 (n + 1)).inv
        = σ i := by
  simp only [ofGeneratorsAndRelations, Functor.leftOp_obj, ofGeneratorsAndRelationsObjMkIso,
    isoOpEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk, id_eq, Iso.unop_hom, SimplicialObject.σ,
    Functor.leftOp_map, Quiver.Hom.unop_op, Iso.unop_inv]
  rw [← unop_comp_assoc, ← unop_comp]
  generalize_proofs p₁ p₂ p₃ p₄ p₅ p₆
  conv_lhs =>
    congr
    rw [← CosimplicialObject.σ, CosimplicialObject.ofGeneratorsAndRelations_map_σ
      (fun n ↦ Opposite.op (X n)) (fun j ↦ (σ j).op) (fun j ↦ (δ j).op) p₁ p₂ p₃ p₄ p₅ p₆ i]
  simp

/-- Up to the same isomorphisms, a simplicial object defined by generators and relations
has the provided functoriality maps for `δ`. -/
@[reassoc (attr := simp)]
lemma ofGeneratorsAndRelations_map_δ {n : ℕ} (i : Fin (n + 2)) :
    (ofGeneratorsAndRelationsObjMkIso X σ δ s1 s2 s3₁ s3₂ s4 s5 (n + 1)).hom ≫
      (ofGeneratorsAndRelations X σ δ s1 s2 s3₁ s3₂ s4 s5).δ i ≫
        (ofGeneratorsAndRelationsObjMkIso X σ δ s1 s2 s3₁ s3₂ s4 s5 n).inv
        = δ i := by
  simp only [ofGeneratorsAndRelations, Functor.leftOp_obj, ofGeneratorsAndRelationsObjMkIso,
    isoOpEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk, id_eq, Iso.unop_hom, SimplicialObject.δ,
    Functor.leftOp_map, Quiver.Hom.unop_op, Iso.unop_inv]
  rw [← unop_comp_assoc, ← unop_comp]
  generalize_proofs p₁ p₂ p₃ p₄ p₅ p₆
  conv_lhs =>
    congr
    rw [← CosimplicialObject.δ, CosimplicialObject.ofGeneratorsAndRelations_map_δ
      (fun n ↦ Opposite.op (X n)) (fun j ↦ (σ j).op) (fun j ↦ (δ j).op) p₁ p₂ p₃ p₄ p₅ p₆ i]
  simp

end MkSimplicialObject

section MkNatTrans

variable (X Y : SimplicialObject C)
  (app : ∀ (Δ : SimplexCategoryᵒᵖ), X.obj Δ ⟶ Y.obj Δ)
  (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), X.δ i ≫ app (.op (.mk n)) = app (.op (.mk (n + 1))) ≫ Y.δ i)
  (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), X.σ i ≫ app (.op (.mk (n + 1))) = app (.op (.mk n)) ≫ Y.σ i)

open SimplexCategoryGenRel in
/-- Construct a natural transformation between simplicial objects out of an application that
commutes with faces and degeneracies. -/
noncomputable def mkNatTrans: X ⟶ Y :=
  NatTrans.removeRightOp <|
    CosimplicialObject.mkNatTrans Y.rightOp X.rightOp
      (fun Δ ↦ (app (.op Δ)).op)
      (fun j ↦ by
        simp only [Functor.rightOp_obj, CosimplicialObject.δ, Functor.rightOp_map]
        rw [← op_comp, ← op_comp]
        congr 1
        exact (hδ j).symm)
      (fun j ↦ by
        simp only [Functor.rightOp_obj, CosimplicialObject.σ, Functor.rightOp_map]
        rw [← op_comp, ← op_comp]
        congr 1
        exact (hσ j).symm)

variable {hδ} {hσ}
/-- The natural transformation built using mkNatTrans have the expected application. -/
@[simp]
lemma mkNatTrans_app (Δ : SimplexCategoryᵒᵖ) : (mkNatTrans X Y app hδ hσ).app Δ = app Δ := by
  dsimp [mkNatTrans]
  generalize_proofs p p'
  rw [CosimplicialObject.mkNatTrans_app Y.rightOp X.rightOp (fun Δ ↦ (app (.op Δ)).op)]
  · simp
  · assumption
  · assumption

lemma mkNatTrans_comp X Y (Z : SimplicialObject C) app
    (app' : ∀ (Δ : SimplexCategoryᵒᵖ), Y.obj Δ ⟶ Z.obj Δ)
    {hδ} {hσ}
    {hδ' : ∀ {n : ℕ} (i : Fin (n + 2)),
      Y.δ i ≫ app' (.op (.mk n)) = app' (.op (.mk (n + 1))) ≫ Z.δ i}
    {hσ' : ∀ {n : ℕ} (i : Fin (n + 1)),
      Y.σ i ≫ app' (.op (.mk (n + 1))) = app' (.op (.mk n)) ≫ Z.σ i}
    : mkNatTrans X Z (fun n ↦ app n ≫ app' n)
        (by intro n i; rw [reassoc_of%(hδ i), hδ' i]; simp)
        (by intro n i; rw [reassoc_of%(hσ i), hσ' i]; simp)
      = (mkNatTrans X Y app hδ hσ) ≫ (mkNatTrans Y Z app' hδ' hσ') := by
  ext Δ
  simp only [mkNatTrans_app, instCategorySimplicialObject_comp_app]
  rw [mkNatTrans_app] <;> assumption

@[simp]
lemma mkNatTrans_id :
  mkNatTrans X X (fun x ↦ 𝟙 _) (by simp) (by simp) = 𝟙 X := by
    ext x
    simp

end MkNatTrans

section MkNatIso

variable (X Y: SimplicialObject C)
  (app : ∀ (Δ : SimplexCategoryᵒᵖ), X.obj Δ ≅ Y.obj Δ)
  (hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
    X.δ i ≫ (app (.op (.mk n))).hom = (app (.op (.mk (n + 1)))).hom ≫ Y.δ i)
  (hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
    X.σ i ≫ (app (.op (.mk (n + 1)))).hom = (app (.op (.mk n))).hom ≫ Y.σ i)

/-- Construct a natural isomorphism between simplicial objects out of an isomorphism that commutes
with faces and degeneracies. -/
noncomputable def mkNatIso: X ≅ Y where
  hom := mkNatTrans X Y (fun x ↦ (app x).hom) hδ hσ
  inv := mkNatTrans Y X (fun x ↦ (app x).inv)
    (by intro n i
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
        exact (hδ i).symm)
    (by intro n i
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
        exact (hσ i).symm)

variable {hδ} {hσ}

@[simp]
lemma mkNatIso_hom_app (Δ : SimplexCategoryᵒᵖ) :
    (mkNatIso X Y app hδ hσ).hom.app Δ = (app Δ).hom := by simp [mkNatIso]

@[simp]
lemma mkNatIso_inv_app (Δ : SimplexCategoryᵒᵖ) :
    (mkNatIso X Y app hδ hσ).inv.app Δ = (app Δ).inv := by
  simp only [mkNatIso]
  generalize_proofs p p'
  rw [mkNatTrans_app] <;> assumption

end MkNatIso

end SimplicialObject

end CategoryTheory
