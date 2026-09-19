/-
Copyright (c) 2025 Terence Rokop.
Copyright (c) 2026 Dzack Garza.

The six relation proofs in this file are adapted from
`anoma/geb@21f75e8bd4ef1ba387840c41d6b694a49a7d7526::geb-lean/GebLean/BarResolution.lean`,
distributed under the GNU General Public License, version 3. This derived file is distributed
under the same license.
-/
module

public import LeanCategories.Homological.CotripleResolution
public import LeanCategories.ForMathlib.SimplicialObjectGeneratorsRelations

/-!
# The simplicial object of a cotriple

This file proves the six simplicial relations for the face and degeneracy maps of
`CotripleResolution` and uses the generators-and-relations constructor to assemble the resulting
simplicial object.

The proofs are ported from
`anoma/geb@21f75e8bd4ef1ba387840c41d6b694a49a7d7526::geb-lean/GebLean/BarResolution.lean`.
That reference proves the relations and constructs a functor on its generators-and-relations
presentation. We use the native `SimplicialObject.ofGeneratorsAndRelations` constructor instead
of porting its arbitrary-simplex-map factorization.

The augmentation follows the standard equivalent presentation of an augmented simplicial object:
an arrow from degree zero whose composites with the two degree-one faces agree. See Weibel,
Construction 8.6.4, and Yun Liu, *Bar Construction*, §5.1, pp. 6--7
(`https://pi.math.cornell.edu/~bts82/events/homotopyF20/notes/bar-construction-typed.pdf`), which
states this compatibility criterion explicitly. For the cotriple construction the equality is
counit naturality. Mathlib's `SimplicialObject.augment` extends it to every degree.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Comonad

universe u v

variable {C : Type u} [Category.{v} C] (T : Comonad C) (A : C)

abbrev faceMap (n : ℕ) : Fin (n + 2) → (T.iterObj A (n + 2) ⟶ T.iterObj A (n + 1)) :=
  T.face A (n + 1)

abbrev degeneracyMap (n : ℕ) :
    Fin (n + 1) → (T.iterObj A (n + 1) ⟶ T.iterObj A (n + 2)) :=
  T.degeneracy A n

private lemma faceMap_zero (n : ℕ) :
    faceMap T A n ⟨0, Nat.zero_lt_succ _⟩ = T.ε.app (T.iterObj A (n + 1)) := by
  cases n <;> rfl

private lemma degeneracyMap_zero (n : ℕ) :
    degeneracyMap T A n ⟨0, Nat.zero_lt_succ _⟩ = T.δ.app (T.iterObj A n) := by
  cases n <;> rfl

private lemma faceMap_succ (n i : ℕ) (hi : i + 1 < n + 1 + 2) :
    faceMap T A (n + 1) ⟨i + 1, hi⟩ =
      T.map (faceMap T A n ⟨i, by omega⟩) := by
  rfl

private lemma degeneracyMap_succ (n i : ℕ) (hi : i + 1 < n + 1 + 1) :
    degeneracyMap T A (n + 1) ⟨i + 1, hi⟩ =
      T.map (degeneracyMap T A n ⟨i, by omega⟩) := by
  rfl

/-- The face-face relation for the cotriple construction. -/
lemma face_comp_face (n i j : ℕ) (hij : i ≤ j) (hi : i < n + 2) (hj : j < n + 2) :
    faceMap T A (n + 1) ⟨j + 1, by omega⟩ ≫ faceMap T A n ⟨i, hi⟩ =
      faceMap T A (n + 1) ⟨i, by omega⟩ ≫ faceMap T A n ⟨j, hj⟩ := by
  induction n generalizing i j with
  | zero =>
    cases i with
    | zero =>
      erw [faceMap_succ, faceMap_zero, faceMap_zero]
      exact @Comonad.counit_naturality C _ T (T.iterObj A 2) (T.iterObj A 1)
        (faceMap T A 0 ⟨j, hj⟩)
    | succ i =>
      have : i = 0 := by omega
      have : j = 1 := by omega
      subst_vars
      erw [faceMap_succ, faceMap_succ, ← T.map_comp, ← T.map_comp]
      congr 1
      exact @Comonad.counit_naturality C _ T (T.iterObj A 1) (T.iterObj A 0) (T.ε.app A)
  | succ n ih =>
    cases i with
    | zero =>
      erw [faceMap_succ, faceMap_zero, faceMap_zero]
      exact @Comonad.counit_naturality C _ T (T.iterObj A (n + 3)) (T.iterObj A (n + 2))
        (faceMap T A (n + 1) ⟨j, hj⟩)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        erw [faceMap_succ, faceMap_succ, faceMap_succ, faceMap_succ,
          ← T.map_comp, ← T.map_comp]
        congr 1
        exact ih i j (by omega) (by omega) (by omega)

/-- The degeneracy-degeneracy relation for the cotriple construction. -/
lemma degeneracy_comp_degeneracy (n i j : ℕ) (hij : i ≤ j)
    (hi : i < n + 1) (hj : j < n + 1) :
    degeneracyMap T A n ⟨i, hi⟩ ≫ degeneracyMap T A (n + 1) ⟨j + 1, by omega⟩ =
      degeneracyMap T A n ⟨j, hj⟩ ≫ degeneracyMap T A (n + 1) ⟨i, by omega⟩ := by
  induction n generalizing i j with
  | zero =>
    have : i = 0 := by omega
    have : j = 0 := by omega
    subst_vars
    erw [degeneracyMap_zero, degeneracyMap_zero, degeneracyMap_succ, degeneracyMap_zero]
    exact T.coassoc (T.iterObj A 0)
  | succ n ih =>
    cases i with
    | zero =>
      cases j with
      | zero =>
        erw [degeneracyMap_zero, degeneracyMap_zero, degeneracyMap_succ, degeneracyMap_zero]
        exact T.coassoc (T.iterObj A (n + 1))
      | succ j =>
        erw [degeneracyMap_zero, degeneracyMap_succ, degeneracyMap_succ, degeneracyMap_zero]
        exact (@Comonad.delta_naturality C _ T (T.iterObj A (n + 1)) (T.iterObj A (n + 2))
          (degeneracyMap T A n ⟨j, by omega⟩)).symm
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        erw [degeneracyMap_succ, degeneracyMap_succ, degeneracyMap_succ,
          degeneracyMap_succ, ← T.map_comp, ← T.map_comp]
        congr 1
        exact ih i j (by omega) (by omega) (by omega)

/-- The first identity case of the mixed face-degeneracy relations. -/
lemma degeneracy_comp_face_self (n j : ℕ) (hj : j < n + 1) :
    degeneracyMap T A n ⟨j, hj⟩ ≫ faceMap T A n ⟨j, by omega⟩ =
      𝟙 (T.iterObj A (n + 1)) := by
  induction n generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst_vars
    erw [degeneracyMap_zero, faceMap_zero]
    exact T.left_counit (T.iterObj A 0)
  | succ n ih =>
    cases j with
    | zero =>
      erw [degeneracyMap_zero, faceMap_zero]
      exact T.left_counit (T.iterObj A (n + 1))
    | succ j =>
      erw [degeneracyMap_succ, faceMap_succ, ← T.map_comp]
      rw [ih j (by omega)]
      exact T.map_id _

/-- The second identity case of the mixed face-degeneracy relations. -/
lemma degeneracy_comp_face_succ (n j : ℕ) (hj : j < n + 1) :
    degeneracyMap T A n ⟨j, hj⟩ ≫ faceMap T A n ⟨j + 1, by omega⟩ =
      𝟙 (T.iterObj A (n + 1)) := by
  induction n generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst_vars
    exact T.right_counit (T.iterObj A 0)
  | succ n ih =>
    cases j with
    | zero =>
      erw [degeneracyMap_zero, faceMap_succ, faceMap_zero]
      exact T.right_counit (T.iterObj A (n + 1))
    | succ j =>
      erw [degeneracyMap_succ, faceMap_succ, ← T.map_comp]
      rw [ih j (by omega)]
      exact T.map_id _

/-- The `i ≤ j` case of the mixed face-degeneracy relations. -/
lemma face_comp_degeneracy_of_le (n i j : ℕ) (hij : i ≤ j)
    (hi : i < n + 2) (hj : j < n + 1) :
    degeneracyMap T A (n + 1) ⟨j + 1, by omega⟩ ≫ faceMap T A (n + 1) ⟨i, by omega⟩ =
      faceMap T A n ⟨i, hi⟩ ≫ degeneracyMap T A n ⟨j, hj⟩ := by
  induction n generalizing i j with
  | zero =>
    have : i = 0 := by omega
    have : j = 0 := by omega
    subst_vars
    erw [degeneracyMap_succ, faceMap_zero, faceMap_zero]
    exact @Comonad.counit_naturality C _ T (T.iterObj A 1) (T.iterObj A 2)
      (degeneracyMap T A 0 ⟨0, by omega⟩)
  | succ n ih =>
    cases i with
    | zero =>
      erw [degeneracyMap_succ, faceMap_zero, faceMap_zero]
      exact @Comonad.counit_naturality C _ T (T.iterObj A (n + 2)) (T.iterObj A (n + 3))
        (degeneracyMap T A (n + 1) ⟨j, by omega⟩)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        erw [degeneracyMap_succ, faceMap_succ, faceMap_succ, degeneracyMap_succ,
          ← T.map_comp, ← T.map_comp]
        congr 1
        exact ih i j (by omega) (by omega) (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- The `j < i` case of the mixed face-degeneracy relations. -/
lemma face_comp_degeneracy_of_gt (n i j : ℕ) (hij : j < i)
    (hi : i < n + 2) (hj : j < n + 1) :
    degeneracyMap T A (n + 1) ⟨j, by omega⟩ ≫ faceMap T A (n + 1) ⟨i + 1, by omega⟩ =
      faceMap T A n ⟨i, hi⟩ ≫ degeneracyMap T A n ⟨j, hj⟩ := by
  induction n generalizing i j with
  | zero =>
    have : j = 0 := by omega
    have : i = 1 := by omega
    subst_vars
    erw [degeneracyMap_zero, faceMap_succ, degeneracyMap_zero]
    exact (@Comonad.delta_naturality C _ T (T.iterObj A 1) (T.iterObj A 0)
      (T.ε.app (T.iterObj A 0))).symm
  | succ n ih =>
    cases j with
    | zero =>
      cases i with
      | zero => omega
      | succ i =>
        erw [degeneracyMap_zero, faceMap_succ, faceMap_succ, degeneracyMap_zero]
        exact (@Comonad.delta_naturality C _ T (T.iterObj A (n + 2)) (T.iterObj A (n + 1))
          (faceMap T A n ⟨i, by omega⟩)).symm
    | succ j =>
      cases i with
      | zero => omega
      | succ i =>
        erw [degeneracyMap_succ, faceMap_succ, ← T.map_comp,
          ih i j (by omega) (by omega) (by omega), T.map_comp, faceMap_succ,
          degeneracyMap_succ]

private lemma relation₁ {n : ℕ} (i j : Fin (n + 2)) (h : i ≤ j) :
    T.face A (n + 2) j.succ ≫ T.face A (n + 1) i =
      T.face A (n + 2) i.castSucc ≫ T.face A (n + 1) j :=
  face_comp_face T A n i j h i.isLt j.isLt

private lemma relation₂ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : i ≤ j.castSucc) :
    T.degeneracy A (n + 1) j.succ ≫ T.face A (n + 2) i.castSucc =
      T.face A (n + 1) i ≫ T.degeneracy A n j :=
  face_comp_degeneracy_of_le T A n i j h i.isLt j.isLt

private lemma relation₃₁ {n : ℕ} (i : Fin (n + 1)) :
    T.degeneracy A n i ≫ T.face A (n + 1) i.castSucc = 𝟙 (T.simplicialDegree A n) :=
  degeneracy_comp_face_self T A n i i.isLt

private lemma relation₃₂ {n : ℕ} (i : Fin (n + 1)) :
    T.degeneracy A n i ≫ T.face A (n + 1) i.succ = 𝟙 (T.simplicialDegree A n) :=
  degeneracy_comp_face_succ T A n i i.isLt

private lemma relation₄ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : j.castSucc < i) :
    T.degeneracy A (n + 1) j.castSucc ≫ T.face A (n + 2) i.succ =
      T.face A (n + 1) i ≫ T.degeneracy A n j :=
  face_comp_degeneracy_of_gt T A n i j h i.isLt j.isLt

private lemma relation₅ {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    T.degeneracy A n j ≫ T.degeneracy A (n + 1) i.castSucc =
      T.degeneracy A n i ≫ T.degeneracy A (n + 1) j.succ :=
  (degeneracy_comp_degeneracy T A n i j h i.isLt j.isLt).symm

/-- The simplicial object whose degree objects and generators are the canonical cotriple formulas.

The augmentation to the constant simplicial object is not part of this declaration. -/
noncomputable def simplicialObject : SimplicialObject C :=
  SimplicialObject.ofGeneratorsAndRelations
    (T.simplicialDegree A)
    (fun {n} i ↦ T.degeneracy A n i)
    (fun {n} i ↦ T.face A (n + 1) i)
    (relation₁ T A) (relation₂ T A) (relation₃₁ T A) (relation₃₂ T A)
    (relation₄ T A) (relation₅ T A)

/-- In degree `n`, the cotriple simplicial object is canonically isomorphic to `T^(n+1)(A)`. -/
noncomputable def simplicialObjectObjIso (n : ℕ) :
    T.simplicialDegree A n ≅ (simplicialObject T A).obj (.op (.mk n)) :=
  SimplicialObject.ofGeneratorsAndRelationsObjMkIso
    (T.simplicialDegree A)
    (fun {n} i ↦ T.degeneracy A n i)
    (fun {n} i ↦ T.face A (n + 1) i)
    (relation₁ T A) (relation₂ T A) (relation₃₁ T A) (relation₃₂ T A)
    (relation₄ T A) (relation₅ T A) n

@[reassoc (attr := simp)]
lemma simplicialObject_map_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (simplicialObjectObjIso T A n).hom ≫ (simplicialObject T A).σ i ≫
      (simplicialObjectObjIso T A (n + 1)).inv = T.degeneracy A n i := by
  exact SimplicialObject.ofGeneratorsAndRelations_map_σ _ _ _
    (relation₁ T A) (relation₂ T A) (relation₃₁ T A) (relation₃₂ T A)
    (relation₄ T A) (relation₅ T A) i

@[reassoc (attr := simp)]
lemma simplicialObject_map_face {n : ℕ} (i : Fin (n + 2)) :
    (simplicialObjectObjIso T A (n + 1)).hom ≫ (simplicialObject T A).δ i ≫
      (simplicialObjectObjIso T A n).inv = T.face A (n + 1) i := by
  exact SimplicialObject.ofGeneratorsAndRelations_map_δ _ _ _
    (relation₁ T A) (relation₂ T A) (relation₃₁ T A) (relation₃₂ T A)
    (relation₄ T A) (relation₅ T A) i

/-- The two degree-one faces have equal composites with the cotriple counit. This is the
augmentation identity in the standard degree-zero presentation of an augmented simplicial
object, and is exactly naturality of the counit applied to `T.ε.app A`. -/
lemma face_comp_augmentation :
    faceMap T A 0 0 ≫ T.augmentation A = faceMap T A 0 1 ≫ T.augmentation A := by
  exact (@Comonad.counit_naturality C _ T (T.iterObj A 1) (T.iterObj A 0)
    (T.ε.app A)).symm

/-- The degree-zero augmentation transported to the assembled simplicial object. -/
noncomputable def simplicialAugmentation :
    (simplicialObject T A).obj (.op (.mk 0)) ⟶ A :=
  (simplicialObjectObjIso T A 0).inv ≫ T.augmentation A

lemma face_comp_simplicialAugmentation :
    (simplicialObject T A).δ 0 ≫ simplicialAugmentation T A =
      (simplicialObject T A).δ 1 ≫ simplicialAugmentation T A := by
  apply (cancel_epi (simplicialObjectObjIso T A 1).hom).1
  simpa only [simplicialAugmentation, Category.assoc, simplicialObject_map_face_assoc] using
    face_comp_augmentation T A

lemma augmentationCondition
    (X : SimplicialObject C) (X₀ : C) (f : X.obj (.op (.mk 0)) ⟶ X₀)
    (h : X.δ 0 ≫ f = X.δ 1 ≫ f) :
    ∀ (i : SimplexCategory) (g₁ g₂ : .mk 0 ⟶ i),
      X.map g₁.op ≫ f = X.map g₂.op ≫ f := by
  intro i g₁ g₂
  let a := g₁.toOrderHom 0
  let b := g₂.toOrderHom 0
  rcases le_total a b with hab | hba
  · let e := SimplexCategory.mkOfLe a b hab
    have hg₁ : g₁ = SimplexCategory.δ 1 ≫ e := by
      ext x
      fin_cases x
      rfl
    have hg₂ : g₂ = SimplexCategory.δ 0 ≫ e := by
      ext x
      fin_cases x
      rfl
    rw [hg₁, hg₂]
    simp only [← op_comp, Functor.map_comp, Category.assoc]
    rw [h]
  · let e := SimplexCategory.mkOfLe b a hba
    have hg₁ : g₁ = SimplexCategory.δ 0 ≫ e := by
      ext x
      fin_cases x
      rfl
    have hg₂ : g₂ = SimplexCategory.δ 1 ≫ e := by
      ext x
      fin_cases x
      rfl
    rw [hg₁, hg₂]
    simp only [← op_comp, Functor.map_comp, Category.assoc]
    rw [h]

/-- Weibel's canonical augmented simplicial object associated to a cotriple. -/
noncomputable def augmentedSimplicialObject : SimplicialObject.Augmented C :=
  SimplicialObject.augment (simplicialObject T A) A (simplicialAugmentation T A)
    (augmentationCondition _ _ _ (face_comp_simplicialAugmentation T A))

end CategoryTheory.Comonad
