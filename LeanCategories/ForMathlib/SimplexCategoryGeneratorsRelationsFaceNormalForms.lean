/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
public import Mathlib.Tactic

/-!
Compatibility port of the face normal forms required by the generators-and-relations
simplex-category equivalence from robin-carlier/mathlib4 commit
9534b44562a606e5a371284ccdf051f6cd47fdda (Apache-2.0), adapted to the pinned Mathlib API.
-/

@[expose] public section

namespace SimplexCategoryGenRel

open CategoryTheory

section NormalFormsP_δ

/-- Given a sequence `L = [i₀, …, iᵣ]`, `standardδ n L` is the composite of the
corresponding face generators.  Its target degree is determined by `L.length`; keeping that
degree in the type avoids the proof-parameter bookkeeping in the original reference port. -/
def standardδ (n : ℕ) : (L : List ℕ) → mk n ⟶ mk (n + L.length)
  | [] => 𝟙 _
  | a :: L =>
      δ (Fin.ofNat (n + 2) a) ≫ standardδ (n + 1) L ≫
        eqToHom (by ext; simp [Nat.add_assoc, Nat.add_comm 1])

/-- `simplicialEvalδ` is a lift to ℕ of `toSimplexCategory.map (standardδ m L)).toOrderHom`,
but we define it this way to enable for less painful inductive reasoning,
and we keep the eqToHom shenanigans in the proof that it is indeed such a lift
(see `simplicialEvalδ_of_IsAdmissible`). It is expected to produce the "correct result" only if
`L` is admissible, but as usual, it is more convenient to have it defined for any list. -/
def simplicialEvalδ (L : List ℕ) : ℕ → ℕ :=
  fun j ↦ match L with
  | [] => j
  | a :: L => simplicialEvalδ L (if j < a then j else j + 1)

variable {n : ℕ} (L : List ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- We prove that simplicialEvalδ is indeed the lift we claimed when the list is admissible. -/
lemma simplicialEvalδ_of_IsAdmissible (hL : IsAdmissible (n + 1) L)
    (j : ℕ) (hj : j < n + 1) :
    ((toSimplexCategory.map (standardδ n L)).toOrderHom ⟨j, hj⟩ : ℕ)
      = simplicialEvalδ L j := by
  induction L generalizing j n with
  | nil =>
    simp [standardδ, simplicialEvalδ]
  | cons a L h_rec =>
    simp only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, standardδ, Functor.map_comp,
      toSimplexCategory_map_δ, SimplexCategory.δ, SimplexCategory.mkHom, eqToHom_map,
      SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom, Nat.add_eq, Nat.add_zero,
      Nat.succ_eq_add_one, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Function.comp_apply,
      Fin.succAboveOrderEmb_apply, Fin.castOrderIso_apply, Fin.coe_cast, simplicialEvalδ]
    have adm_L : IsAdmissible (n + 1 + 1) L := hL.of_cons
    have ha : a < n + 2 := by
      simpa [Nat.add_assoc] using hL.head.prop
    split_ifs with hj₁
    · rw [Fin.succAbove_of_castSucc_lt]
      · simpa [SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom] using
          h_rec (n := n + 1) (j := j) (hj := Nat.lt_succ_of_lt hj) adm_L
      · simpa [Fin.lt_def, Nat.mod_eq_of_lt ha] using hj₁
    · rw [Fin.succAbove_of_le_castSucc]
      · simp only [Fin.succ_mk]
        simpa [SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom] using
          h_rec (n := n + 1) (j := j + 1) (hj := by omega) adm_L
      · simp only [not_lt] at hj₁
        simpa [Fin.le_iff_val_le_val, Nat.mod_eq_of_lt ha] using hj₁

lemma simplicialEvalδ_monotone : Monotone (simplicialEvalδ L) := by
  intro a b hab
  induction L generalizing a b with
  | nil => exact hab
  | cons head tail h_rec =>
    dsimp only [simplicialEvalδ]
    split_ifs with h h' h'
    · exact h_rec hab
    · have hab' : a ≤ b + 1 := by omega
      exact h_rec hab'
    · have hab' : a + 1 ≤ b := by omega
      exact h_rec hab'
    · exact h_rec (Nat.succ_le_succ hab)

variable (j : ℕ)

lemma le_simplicialEvalδ_self : j ≤ simplicialEvalδ L j := by
  induction L generalizing j with
  | nil => simp [simplicialEvalδ]
  | cons head tail h_rec =>
    dsimp only [simplicialEvalδ]
    split_ifs with h
    · haveI := h_rec j
      omega
    · have hj := simplicialEvalδ_monotone tail (j.le_succ)
      haveI := h_rec j
      exact this.trans hj

lemma simplicialEvalδ_eq_self_of_IsAdmissible_and_lt (hL : IsAdmissible (n + 1) L)
    (hj : ∀ k ∈ L, j < k) : simplicialEvalδ L j = j := by
  induction L generalizing n j with
  | nil => simp [simplicialEvalδ]
  | cons a L h_rec =>
    dsimp only [simplicialEvalδ]
    split_ifs with h
    · apply h_rec _ (hL.of_cons)
      simp only [List.mem_cons, forall_eq_or_imp] at hj
      exact hj.right
    · simp only [not_lt] at h
      simp only [List.mem_cons, forall_eq_or_imp] at hj
      obtain ⟨hj₁, hj₂⟩ := hj
      linarith

lemma simplicialEvalδ_eq_self_of_IsAdmissible_cons (a : ℕ)
    (hL : IsAdmissible (n + 1) (a :: L)) : simplicialEvalδ L a = a := by
  apply simplicialEvalδ_eq_self_of_IsAdmissible_and_lt _ _ hL.of_cons
  exact hL.head_lt

/-- Performing a simplicial insert in a list is, up to the target-degree identification,
composition on the right by the corresponding face operator. -/
lemma standardδ_simplicialInsert_heq
    (hL : IsAdmissible (n + 2) L) (j : ℕ) (hj : j < n + 2) :
    standardδ n (simplicialInsert j L) ≍
      δ (Fin.ofNat (n + 2) j) ≫ standardδ (n + 1) L := by
  induction L generalizing n j with
  | nil =>
    simp [standardδ, simplicialInsert]
  | cons a L h_rec =>
    by_cases h : j < a
    · have hins : simplicialInsert j (a :: L) = j :: a :: L := by
        simp [simplicialInsert, h]
      rw [hins]
      change
        (δ (Fin.ofNat (n + 2) j) ≫ standardδ (n + 1) (a :: L) ≫ eqToHom _) ≍
          δ (Fin.ofNat (n + 2) j) ≫ standardδ (n + 1) (a :: L)
      rw [← Category.assoc]
      exact CategoryTheory.comp_eqToHom_heq (C := SimplexCategoryGenRel) _ _
    · have hins :
          simplicialInsert j (a :: L) = a :: simplicialInsert (j + 1) L := by
        simp [simplicialInsert, h]
      rw [hins]
      have h_rec' := h_rec hL.of_cons (j + 1) (by omega)
      have htarget :
          mk ((n + 1) + (simplicialInsert (j + 1) L).length) =
            mk ((n + 2) + L.length) := by
        apply congrArg mk
        rw [simplicialInsert_length]
        omega
      have hcomp :
          δ (Fin.ofNat (n + 2) a) ≫ standardδ (n + 1) (simplicialInsert (j + 1) L) ≍
            δ (Fin.ofNat (n + 2) a) ≫
              (δ (Fin.ofNat (n + 3) (j + 1)) ≫ standardδ (n + 2) L) :=
        heq_comp rfl rfl htarget (HEq.rfl) h_rec'
      have ha : a < n + 2 := by omega
      have simplicial_id := δ_comp_δ_nat (n := n) a j ha hj (by omega)
      generalize_proofs p p' at simplicial_id
      have ha₁ : (⟨a, ha⟩ : Fin (n + 2)) = Fin.ofNat (n + 2) a := by
        ext
        simp [Nat.mod_eq_of_lt ha]
      have ha₂ : (⟨a, p'⟩ : Fin (n + 3)) = Fin.ofNat (n + 3) a := by
        ext
        simp [Nat.mod_eq_of_lt p']
      have hj₁ : (⟨j + 1, p⟩ : Fin (n + 3)) = Fin.ofNat (n + 3) (j + 1) := by
        ext
        simp [Nat.mod_eq_of_lt p]
      have hj₂ : (⟨j, hj⟩ : Fin (n + 2)) = Fin.ofNat (n + 2) j := by
        ext
        simp [Nat.mod_eq_of_lt hj]
      rw [← ha₁, ← hj₁] at hcomp
      have hmid :
          δ (⟨a, ha⟩ : Fin (n + 2)) ≫
              (δ (⟨j + 1, p⟩ : Fin (n + 3)) ≫ standardδ (n + 2) L) =
            δ (⟨j, hj⟩ : Fin (n + 2)) ≫
              (δ (⟨a, p'⟩ : Fin (n + 3)) ≫ standardδ (n + 2) L) := by
        simpa only [Category.assoc] using
          congrArg (fun q => q ≫ standardδ (n + 2) L) simplicial_id
      have hraw :=
        hcomp.trans (heq_of_eq hmid)
      have hstd :
          standardδ (n + 1) (a :: L) ≍
            δ (Fin.ofNat (n + 3) a) ≫ standardδ (n + 2) L := by
        change
          (δ (Fin.ofNat (n + 3) a) ≫ standardδ (n + 2) L ≫ eqToHom _) ≍
            δ (Fin.ofNat (n + 3) a) ≫ standardδ (n + 2) L
        rw [← Category.assoc]
        exact comp_eqToHom_heq _ _
      have htarget' :
          mk ((n + 1) + (a :: L).length) = mk ((n + 2) + L.length) := by
        apply congrArg mk
        simp only [List.length_cons]
        omega
      have hrhs :
          δ (Fin.ofNat (n + 2) j) ≫ standardδ (n + 1) (a :: L) ≍
            δ (Fin.ofNat (n + 2) j) ≫
              (δ (Fin.ofNat (n + 3) a) ≫ standardδ (n + 2) L) :=
        heq_comp rfl rfl htarget' (HEq.rfl) hstd
      rw [ha₁, ha₂, hj₂] at hraw
      have houter :
          standardδ n (a :: simplicialInsert (j + 1) L) ≍
            δ (Fin.ofNat (n + 2) a) ≫
              standardδ (n + 1) (simplicialInsert (j + 1) L) := by
        change
          (δ (Fin.ofNat (n + 2) a) ≫
              standardδ (n + 1) (simplicialInsert (j + 1) L) ≫ eqToHom _) ≍
            δ (Fin.ofNat (n + 2) a) ≫
              standardδ (n + 1) (simplicialInsert (j + 1) L)
        rw [← Category.assoc]
        exact comp_eqToHom_heq _ _
      exact houter.trans (hraw.trans hrhs.symm)

/-- Equality-valued form of `standardδ_simplicialInsert_heq`, with the target
identification made explicit. -/
lemma standardδ_simplicialInsert (hL : IsAdmissible (n + 2) L) (j : ℕ) (hj : j < n + 2) :
    standardδ n (simplicialInsert j L) =
        δ (Fin.ofNat (n + 2) j) ≫ standardδ (n + 1) L ≫
          eqToHom (by
            ext
            simp [simplicialInsert_length, Nat.add_assoc, Nat.add_comm 1]) := by
  rw [← heq_iff_eq]
  simpa only [Category.assoc] using
    (heq_comp_eqToHom_iff _ _ _).2 (standardδ_simplicialInsert_heq L hL j hj)

/-- Using the above property, we can prove that every morphism satisfying `P_δ` is equal to some
`standardδ` for some admissible list of indices. Because morphisms of the form `standardδ` have a
rather  constrained sources and targets, we have again to splice in some `eqToHom`'s to make
everything work. -/
theorem exists_normal_form_P_δ {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_δ f) :
    ∃ L : List ℕ,
    ∃ m : ℕ,
    ∃ h₁ : x = mk m,
    ∃ h₂ : mk (m + L.length) = y,
    (IsAdmissible (m + 1) L) ∧ f = eqToHom h₁ ≫ standardδ m L ≫ eqToHom h₂ := by
  change faces.multiplicativeClosure f at hf
  rw [MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure'] at hf
  induction hf with
  | id x =>
    let n := x.len
    have hx : x = mk n := by
      apply SimplexCategoryGenRel.ext
      simp [n]
    use [], n, hx, by simpa using hx.symm, IsAdmissible.nil _
    simpa [standardδ] using (Category.eqToHom_trans hx hx.symm).symm
  | of f hf =>
    cases hf with
    | @δ n j =>
      use [j.val], n, rfl, by simp, IsAdmissible.singleton j.is_le
      simp [standardδ, Nat.mod_eq_of_lt j.is_lt]
  | @of_comp x' x'' y' f g hf hg h_rec =>
    cases hf with
    | @δ m j =>
      obtain ⟨L₁, m₁, h₁', h₂', hL₁, e₁⟩ := h_rec
      have hm₁ : m + 1 = m₁ := by
        simpa using congrArg SimplexCategoryGenRel.len h₁'
      subst m₁
      refine ⟨simplicialInsert j.val L₁, m, rfl, ?_, ?_, ?_⟩
      · have htarget :
            mk (m + (simplicialInsert j.val L₁).length) =
              mk ((m + 1) + L₁.length) := by
          ext
          simp [simplicialInsert_length, Nat.add_assoc, Nat.add_comm 1]
        exact htarget.trans h₂'
      · exact simplicialInsert_isAdmissible (m + 1) L₁ hL₁ j.val j.is_le
      · rw [e₁]
        simp only [eqToHom_refl, Category.id_comp]
        rw [standardδ_simplicialInsert L₁ hL₁ j.val j.is_lt]
        simp only [Category.assoc]
        have hjfin : Fin.ofNat (m + 2) j.val = j := by
          ext
          simp [Nat.mod_eq_of_lt j.is_lt]
        rw [hjfin]
        congr 1
        simp only [eqToHom_trans]

private lemma head_eq_head_of_simplicialEvalδ_eq
    (L₁ : List ℕ) (a : ℕ) (hL₁ : IsAdmissible (n + 1) (a :: L₁))
    (L₂ : List ℕ) (b : ℕ) (hL₂ : IsAdmissible (n + 1) (b :: L₂))
    (h : ∀ x < n + 1, simplicialEvalδ (a::L₁) x = simplicialEvalδ (b::L₂) x) :
    a = b := by
  have ha₁ := h a
  simp only [simplicialEvalδ, lt_self_iff_false, ↓reduceIte] at ha₁
  have hb₁ := h b
  simp only [simplicialEvalδ, lt_self_iff_false, ↓reduceIte] at hb₁
  split_ifs at ha₁ with ha₂ <;> split_ifs at hb₁ with hb₂
  · omega
  · exfalso
    haveI : simplicialEvalδ L₂ a = a := by
      apply simplicialEvalδ_eq_self_of_IsAdmissible_and_lt L₂ _ (hL₂.of_cons)
      intro k hk
      exact ha₂.trans (hL₂.head_lt k hk)
    rw [this] at ha₁
    haveI := le_simplicialEvalδ_self L₁ (a + 1)
    obtain hb | hb := Nat.lt_add_one_iff_lt_or_eq.mp hL₂.head.prop
    · haveI := hb₁ hb
      haveI := ha₁ (ha₂.trans hb)
      linarith
    · have hb' : b = n + 1 := by simpa using hb
      subst hb'
      omega
  · exfalso
    haveI : simplicialEvalδ L₁ b = b := by
      apply simplicialEvalδ_eq_self_of_IsAdmissible_and_lt L₁ _ (hL₁.of_cons)
      intro k hk
      exact hb₂.trans (hL₁.head_lt k hk)
    rw [this] at hb₁
    haveI := le_simplicialEvalδ_self L₂ (b + 1)
    obtain ha | ha := Nat.lt_add_one_iff_lt_or_eq.mp hL₁.head.prop
    · haveI := ha₁ ha
      haveI := hb₁ (hb₂.trans ha)
      linarith
    · have ha' : a = n + 1 := by simpa using ha
      subst ha'
      omega
  · omega

/-- Again, the key point is that admissible lists are determined by simplicialEvalδ, which only
depends on the realization of `standardδ` in the usual simplex category. -/
lemma eq_of_simplicialEvalδ_eq
    (L₁ : List ℕ) (hL₁ : IsAdmissible (n + 1) L₁)
    (L₂ : List ℕ) (hL₂ : IsAdmissible (n + 1) L₂)
    (h : ∀ x < n + 1, simplicialEvalδ L₁ x = simplicialEvalδ L₂ x) :
    (L₁.length = L₂.length) → (L₁ = L₂) := by
  induction L₁ generalizing L₂ n with
  | nil =>
    intro a
    symm at a ⊢
    simpa using a
  | cons a L₁ hrec =>
    cases L₂ with
    | nil => tauto
    | cons b L₂ =>
      haveI : a = b := head_eq_head_of_simplicialEvalδ_eq L₁ a hL₁ L₂ b hL₂ h
      subst this
      simp only [List.cons.injEq, true_and]
      intro h_length
      apply hrec (hL₁.of_cons) _ (hL₂.of_cons)
      · intro x hx
        obtain hx | hx := Nat.lt_add_one_iff_lt_or_eq.mp hx
        · haveI := h x hx
          by_cases hax : x < a
          · simpa [simplicialEvalδ, hax] using this
          · haveI := h x
            simp only [simplicialEvalδ] at this
            simp only [not_lt] at hax
            split_ifs at this with hax₁
            · exact this hx
            · cases x with
              | zero =>
                haveI : a = 0 := by omega
                subst this
                rw [simplicialEvalδ_eq_self_of_IsAdmissible_cons L₁ 0 hL₁
                  , simplicialEvalδ_eq_self_of_IsAdmissible_cons L₂ 0 hL₂]
              | succ x =>
                haveI := h x (Nat.lt_of_add_right_lt hx)
                simp only [simplicialEvalδ] at this
                split_ifs at this
                · simp at hax₁
                  haveI : a = x + 1 := by omega
                  subst this
                  rw [simplicialEvalδ_eq_self_of_IsAdmissible_cons L₁ (x + 1) hL₁
                    , simplicialEvalδ_eq_self_of_IsAdmissible_cons L₂ (x + 1) hL₂]
                · linarith
        · subst hx
          obtain ha | ha := Nat.lt_add_one_iff_lt_or_eq.mp hL₁.head.prop
          · haveI := h n (by simp)
            simp only [simplicialEvalδ] at this
            have ha' : a < n + 1 := by simpa using ha
            split_ifs at this <;> omega
          · have ha' : a = n + 1 := by simpa using ha
            subst ha'
            rw [simplicialEvalδ_eq_self_of_IsAdmissible_cons L₁ (n + 1) hL₁
              , simplicialEvalδ_eq_self_of_IsAdmissible_cons L₂ (n + 1) hL₂]
      · simpa using h_length

end NormalFormsP_δ


end SimplexCategoryGenRel
