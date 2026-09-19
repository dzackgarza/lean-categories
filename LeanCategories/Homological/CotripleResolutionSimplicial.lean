/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

The augmentation natural transformation is not constructed here.
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

/-- The simplicial object whose degree objects and generators are the canonical cotriple formulas.

The augmentation to the constant simplicial object is not part of this declaration. -/
noncomputable def simplicialObject : SimplicialObject C :=
  SimplicialObject.ofGeneratorsAndRelations
    (T.simplicialDegree A)
    (T.degeneracy A)
    (fun i ↦ T.face A _ i)
    (fun i j h ↦ face_comp_face T A _ i j h i.isLt j.isLt)
    (fun i j h ↦ face_comp_degeneracy_of_le T A _ i j h i.isLt j.isLt)
    (fun i ↦ degeneracy_comp_face_self T A _ i i.isLt)
    (fun i ↦ degeneracy_comp_face_succ T A _ i i.isLt)
    (fun i j h ↦ face_comp_degeneracy_of_gt T A _ i j h i.isLt j.isLt)
    (fun i j h ↦ degeneracy_comp_degeneracy T A _ i j h i.isLt j.isLt)

/-- In degree `n`, the cotriple simplicial object is canonically isomorphic to `T^(n+1)(A)`. -/
noncomputable def simplicialObjectObjIso (n : ℕ) :
    T.simplicialDegree A n ≅ (T.simplicialObject A).obj (.op (.mk n)) :=
  SimplicialObject.ofGeneratorsAndRelationsObjMkIso _ _ _ _ _ _ _ _ _ n

@[reassoc (attr := simp)]
lemma simplicialObject_map_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    (T.simplicialObjectObjIso A n).hom ≫ (T.simplicialObject A).σ i ≫
      (T.simplicialObjectObjIso A (n + 1)).inv = T.degeneracy A n i := by
  apply SimplicialObject.ofGeneratorsAndRelations_map_σ

@[reassoc (attr := simp)]
lemma simplicialObject_map_face {n : ℕ} (i : Fin (n + 2)) :
    (T.simplicialObjectObjIso A (n + 1)).hom ≫ (T.simplicialObject A).δ i ≫
      (T.simplicialObjectObjIso A n).inv = T.face A (n + 1) i := by
  apply SimplicialObject.ofGeneratorsAndRelations_map_δ

end CategoryTheory.Comonad
