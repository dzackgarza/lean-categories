/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import LeanCategories.ForMathlib.SimplexCategoryGeneratorsRelationsFaceNormalForms

@[expose] public section
/-! # Equivalence between `SimplexCategoryGenRel` and `SimplexCategory`.

In this file, we establish that `toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory` is
an equivalence of categories. We introduce `equivSimplexCategory` as this equivalence.

## References:
* [Kerodon Tag 04FW](https://kerodon.net/tag/04FW)
* Robin Carlier, mathlib PR #25741, commit
  `9534b44562a606e5a371284ccdf051f6cd47fdda`,
  `Mathlib/AlgebraicTopology/SimplexCategory/GeneratorsRelations/Equivalence.lean`.

-/
namespace SimplexCategoryGenRel

open CategoryTheory

section EquivalenceWithSimplexCategory

private lemma admissible_ext {m : ℕ} {L₁ L₂ : List ℕ}
    (hL₁ : IsAdmissible m L₁) (hL₂ : IsAdmissible m L₂)
    (hmem : ∀ x, x ∈ L₁ ↔ x ∈ L₂) : L₁ = L₂ := by
  apply List.Perm.eq_of_sortedLE hL₁.sortedLT.sortedLE hL₂.sortedLT.sortedLE
  exact (List.perm_ext_iff_of_nodup hL₁.sortedLT.nodup hL₂.sortedLT.nodup).2 hmem

-- Marked private as the stronger statement with unicity is below.
/-- Every epimorphism in the usual simplex category can be represented in SimplexCategoryGenRel by
a morphism satisfying `P_σ`. -/
private lemma exists_P_σ_of_epi {m k : ℕ} (f : SimplexCategory.mk (m + k) ⟶ .mk m)
    (hf : Epi f) : ∃ (g : SimplexCategoryGenRel.mk (m + k) ⟶ .mk m),
      P_σ g ∧ toSimplexCategory.map g = f := by
  induction k with
  | zero =>
    dsimp only [Nat.add_zero] at f
    haveI : f = 𝟙 _ := SimplexCategory.eq_id_of_epi _
    subst this
    exact ⟨𝟙 _, P_σ.id_mem _, by simp⟩
  | succ k h_rec =>
    have eq_1 : SimplexCategory.mk (m + k + 1) = SimplexCategory.mk (m + (k + 1)) := by
      rw [Nat.add_assoc]
    let f' := eqToHom eq_1 ≫ f
    have f'_epi : Epi f' := by apply epi_comp
    haveI : ¬(Function.Injective f'.toOrderHom) := by
      intro h
      rw [← SimplexCategory.mono_iff_injective] at h
      have le := SimplexCategory.len_lt_of_mono f'
        (by intro h0
            apply_fun (fun x ↦ x.len) at h0
            simp only [SimplexCategory.len_mk] at h0
            linarith)
      simp only [SimplexCategory.len_mk] at le
      linarith
    obtain ⟨j₀, f₀, hf₀⟩ := SimplexCategory.eq_σ_comp_of_not_injective _ this
    haveI : Epi f₀ := by
      rw [hf₀] at f'_epi
      apply CategoryTheory.epi_of_epi (SimplexCategory.σ j₀)
    obtain ⟨g₀, hg₀⟩ := h_rec f₀ this
    use (σ j₀ ≫ g₀)
    constructor
    · exact P_σ.comp_mem _ _ (P_σ.σ _) hg₀.left
    · rw [Functor.map_comp, hg₀.right, toSimplexCategory_map_σ]
      simpa [f', Nat.add_assoc] using hf₀.symm

/-- Every epimorphism in the usual simplex category can be uniquely represented in
`SimplexCategoryGenRel` by a morphism satisfying `P_σ`. -/
theorem existsUnique_P_σ_of_epi {m k : ℕ} (f : SimplexCategory.mk (m + k) ⟶ .mk m)
    (hf : Epi f) : ∃! (g : SimplexCategoryGenRel.mk (m + k) ⟶ .mk m),
      P_σ g ∧ toSimplexCategory.map g = f := by
  -- We already established existence.
  apply existsUnique_of_exists_of_unique (exists_P_σ_of_epi _ hf)
  rintro g₁ g₂ ⟨hg₁, hg₁'⟩ ⟨hg₂, hg₂'⟩
  obtain ⟨L₁, m₁, b₁, he₁, he₁', hL₁, hL₁_adm, h_comp₁⟩ := exists_normal_form_P_σ g₁ hg₁
  obtain ⟨L₂, m₂, b₂, he₂, he₂', hL₂, hL₂_adm, h_comp₂⟩ := exists_normal_form_P_σ g₂ hg₂
  -- Eliminate as much eqToHom as we can by substitutions, this is just "noise".
  have h₁ : m₁ = m₂ := by
    haveI := he₂.trans he₁.symm |>.symm
    apply_fun (fun x ↦ x.len) at this
    exact this
  have h₂ : m = m₁ := by
    haveI := he₁.symm
    apply_fun (fun x ↦ x.len) at this
    exact this
  subst h₁
  subst h₂
  have h₃ : b₁ = k := by
    haveI := he₁'.symm
    apply_fun (fun x ↦ x.len) at this
    simpa using this
  have h₄ : b₂ = k := by
    haveI := he₂'.symm
    apply_fun (fun x ↦ x.len) at this
    simpa using this
  subst h₃
  subst h₄
  symm at hL₂
  subst hL₂
  -- The "actual proof" starts here: it suffices to show the indices in the normal
  -- forms are the same, and they are characterized by simplicialEvalσ, which only cares
  -- about the order hom associated with the morphisms.
  suffices hL₁₂ : L₁ = L₂ by
    subst hL₁₂
    rw [h_comp₁, h_comp₂]
  apply admissible_ext hL₁_adm hL₂_adm
  intro x
  apply (mem_isAdmissible_iff L₁ hL₁_adm x).trans
  rw [mem_isAdmissible_iff L₂ hL₂_adm x]
  have h_length : L₁.length = L₂.length := by
    rwa [← hL₂] at hL₁
  rw [h_length]
  try simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h_comp₁ h_comp₂
  subst h_comp₂ h_comp₁
  symm at hg₁'
  subst hg₁'
  apply and_congr_right
  intro hx
  rw [← simplicialEvalσ_of_isAdmissible L₁ (m + L₂.length) m hL₁_adm
      (by simpa [hL₁]) _ (hx.trans (lt_add_one _)),
    ← simplicialEvalσ_of_isAdmissible L₂ (m + L₂.length) m hL₂_adm rfl _
      (hx.trans (lt_add_one _)),
    ← simplicialEvalσ_of_isAdmissible L₁ (m + L₂.length) m hL₁_adm
      (by simpa [hL₁]) _ (Nat.succ_lt_succ hx),
    ← simplicialEvalσ_of_isAdmissible L₂ (m + L₂.length) m hL₂_adm rfl _
      (Nat.succ_lt_succ hx)]
  have h₀ := congrArg
    (fun q => q.toOrderHom ⟨x, by simpa using hx.trans (lt_add_one _)⟩) hg₂'
  have h₁ := congrArg
    (fun q => q.toOrderHom ⟨x + 1, by simpa using Nat.succ_lt_succ hx⟩) hg₂'
  have h₀' := congrArg Fin.val h₀
  have h₁' := congrArg Fin.val h₁
  constructor
  · intro h
    exact h₀'.trans (h.trans h₁'.symm)
  · intro h
    exact h₀'.symm.trans (h.trans h₁')

-- Marked private as the stronger statement with unicity is below.
private lemma exists_P_δ_of_mono {m k : ℕ} (f : SimplexCategory.mk m ⟶ .mk (m + k))
    (hf : Mono f) : ∃ (g : SimplexCategoryGenRel.mk m ⟶ .mk (m + k)),
      P_δ g ∧ toSimplexCategory.map g = f := by
  induction k with
  | zero =>
    dsimp only [Nat.add_zero] at f
    haveI : f = 𝟙 _ := SimplexCategory.eq_id_of_mono _
    subst this
    exact ⟨𝟙 _, P_δ.id_mem _, by simp⟩
  | succ k h_rec =>
    have eq_1 : SimplexCategory.mk (m + k + 1) = SimplexCategory.mk (m + (k + 1)) := by
      rw [Nat.add_assoc]
    let f' := f ≫ eqToHom eq_1
    have f'_mono : Mono f' := by apply mono_comp
    haveI : ¬(Function.Surjective f'.toOrderHom) := by
      intro h
      rw [← SimplexCategory.epi_iff_surjective] at h
      have le := SimplexCategory.len_le_of_epi f'
      simp only [SimplexCategory.len_mk] at le
      linarith
    obtain ⟨j₀, f₀, hf₀⟩ := SimplexCategory.eq_comp_δ_of_not_surjective _ this
    haveI : Mono f₀ := by
      rw [hf₀] at f'_mono
      exact CategoryTheory.mono_of_mono f₀ (SimplexCategory.δ j₀)
    obtain ⟨g₀, hg₀⟩ := h_rec f₀ this
    use (g₀ ≫ δ j₀)
    constructor
    · exact P_δ.comp_mem _ _ hg₀.left (P_δ.δ _)
    · rw [Functor.map_comp, hg₀.right, toSimplexCategory_map_δ]
      simpa [f', Nat.add_assoc] using hf₀.symm

/-- Every epimorphism in the usual simplex category can be uniquely represented in
`SimplexCategoryGenRel` by a morphism satisfying `P_δ`. -/
theorem existsUnique_P_δ_of_mono {m k : ℕ} (f : SimplexCategory.mk m ⟶ .mk (m + k))
    (hf : Mono f) : ∃! (g : SimplexCategoryGenRel.mk m ⟶ .mk (m + k)),
      P_δ g ∧ toSimplexCategory.map g = f := by
  apply existsUnique_of_exists_of_unique (exists_P_δ_of_mono _ hf)
  rintro g₁ g₂ ⟨hg₁, hg₁'⟩ ⟨hg₂, hg₂'⟩
  obtain ⟨L₁, m₁, he₁, he₁', hL₁_adm, h_comp₁⟩ := exists_normal_form_P_δ g₁ hg₁
  obtain ⟨L₂, m₂, he₂, he₂', hL₂_adm, h_comp₂⟩ := exists_normal_form_P_δ g₂ hg₂
  -- Again get rid of eqToHoms by substitutions
  have hm₁ : m = m₁ := by simpa using congrArg SimplexCategoryGenRel.len he₁
  have hm₂ : m = m₂ := by simpa using congrArg SimplexCategoryGenRel.len he₂
  subst m₁
  subst m₂
  have hL₁ : L₁.length = k := by
    have h := congrArg SimplexCategoryGenRel.len he₁'
    simpa using h
  have hL₂ : L₂.length = k := by
    have h := congrArg SimplexCategoryGenRel.len he₂'
    simpa using h
  suffices hL₁₂ : L₁ = L₂ by
    subst hL₁₂
    rw [h_comp₁, h_comp₂]
  try simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h_comp₁ h_comp₂
  subst h_comp₂ h_comp₁
  symm at hg₁'
  subst hg₁'
  apply eq_of_simplicialEvalδ_eq L₁ hL₁_adm L₂ hL₂_adm
  · intro x hx
    rw [← simplicialEvalδ_of_IsAdmissible L₁ hL₁_adm x hx,
      ← simplicialEvalδ_of_IsAdmissible L₂ hL₂_adm x hx]
    have h := congrArg
      (fun q => q.toOrderHom ⟨x, by simpa using hx⟩) hg₂'
    have hv := congrArg Fin.val h
    have hcast {a b c : SimplexCategory} (q : a ⟶ b) (e : b = c)
        (j : Fin (a.len + 1)) :
        ((q ≫ eqToHom e).toOrderHom j).val = (q.toOrderHom j).val := by
      cases e
      simp
    simp only [Functor.map_comp, eqToHom_map] at hv
    rw [hcast, hcast] at hv
    exact hv.symm
  · exact hL₁.trans hL₂.symm

set_option backward.isDefEq.respectTransparency false in
theorem existsUnique_toSimplexCategory_map
    {x y : SimplexCategoryGenRel}
    (f : toSimplexCategory.obj x ⟶ toSimplexCategory.obj y)
    : ∃! g: x ⟶ y, toSimplexCategory.map g = f := by
  induction x using SimplexCategoryGenRel.rec <;>
    induction y using SimplexCategoryGenRel.rec
  rename_i n m
  change SimplexCategory.mk n ⟶ SimplexCategory.mk m at f
  let strong_fac_f := (Limits.HasStrongEpiMonoFactorisations.has_fac f).some
  let z := strong_fac_f.I
  let epi₀ := strong_fac_f.toMonoFactorisation.e
  let mono₀ := strong_fac_f.toMonoFactorisation.m
  have fac : epi₀ ≫ mono₀ = f := strong_fac_f.fac
  letI : Epi epi₀ := strong_fac_f.e_strong_epi.epi
  letI : Mono mono₀ := strong_fac_f.m_mono
  have h_epi : z.len ≤ n := by
    simpa [epi₀, z, strong_fac_f] using SimplexCategory.len_le_of_epi epi₀
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h_epi
  have h_mono : z.len ≤ m := by
    simpa [mono₀, z, strong_fac_f] using SimplexCategory.len_le_of_mono mono₀
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le h_mono
  let p₁ : mk n = mk (z.len + k) := SimplexCategoryGenRel.ext hk
  let p₂ : mk (z.len + l) = mk m := SimplexCategoryGenRel.ext hl.symm
  let q₁ : SimplexCategory.mk n = SimplexCategory.mk (z.len + k) :=
    SimplexCategory.ext hk
  let q₂ : SimplexCategory.mk (z.len + l) = SimplexCategory.mk m :=
    SimplexCategory.ext hl.symm
  let epi₁ : SimplexCategory.mk (z.len + k) ⟶ SimplexCategory.mk z.len :=
    eqToHom q₁.symm ≫ epi₀
  let mono₁ : SimplexCategory.mk z.len ⟶ SimplexCategory.mk (z.len + l) :=
    mono₀ ≫ eqToHom q₂.symm
  have hp₁ : toSimplexCategory.map (eqToHom p₁) = eqToHom q₁ := by
    simp [q₁, eqToHom_map]
  have hp₁' : toSimplexCategory.map (eqToHom p₁.symm) = eqToHom q₁.symm := by
    simp [q₁, eqToHom_map]
  have hp₂ : toSimplexCategory.map (eqToHom p₂) = eqToHom q₂ := by
    simp [q₂, eqToHom_map]
  have hp₂' : toSimplexCategory.map (eqToHom p₂.symm) = eqToHom q₂.symm := by
    simp [q₂, eqToHom_map]
  haveI : Epi (eqToHom q₁.symm) := by infer_instance
  haveI : Mono (eqToHom q₂.symm) := by infer_instance
  have hEpi₁ : Epi epi₁ := by
    change Epi (eqToHom q₁.symm ≫ epi₀)
    infer_instance
  have hMono₁ : Mono mono₁ := by
    change Mono (mono₀ ≫ eqToHom q₂.symm)
    infer_instance
  letI : Epi epi₁ := hEpi₁
  letI : Mono mono₁ := hMono₁
  obtain ⟨e₁, ⟨P_σ_e₁, he₁⟩, he₁'⟩ :=
    @existsUnique_P_σ_of_epi z.len k epi₁ hEpi₁
  obtain ⟨m₁, ⟨P_δ_m₁, hm₁⟩, hm₁'⟩ :=
    @existsUnique_P_δ_of_mono z.len l mono₁ hMono₁
  refine ⟨eqToHom p₁ ≫ e₁ ≫ m₁ ≫ eqToHom p₂, ?_, ?_⟩
  · simp only [Functor.map_comp, he₁, hm₁]
    rw [hp₁, hp₂]
    change eqToHom q₁ ≫ epi₁ ≫ mono₁ ≫ eqToHom q₂ = f
    simpa only [epi₁, mono₁, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] using fac
  intro g hg
  obtain ⟨z₁, e₂, m₂, P_σ_e₂, P_δ_m₂, fac₂⟩ := exists_P_σ_P_δ_factorization g
  rw [fac₂] at hg
  haveI : IsSplitEpi (toSimplexCategory.map e₂) :=
    isSplitEpi_toSimplexCategory_map_of_P_σ P_σ_e₂
  haveI : IsSplitMono (toSimplexCategory.map m₂) :=
    isSplitMono_toSimplexCategory_map_of_P_δ P_δ_m₂
  simp only [Functor.map_comp] at hg
  have im₁ := SimplexCategory.image_eq hg
  have im₂ := SimplexCategory.image_eq fac
  have hz : toSimplexCategory.obj z₁ = z := im₁.symm.trans im₂
  have eq_z₁ : z₁ = mk z.len := by
    apply SimplexCategoryGenRel.ext
    have h := congrArg SimplexCategory.len hz
    simpa [toSimplexCategory_len] using h
  let e₃ := toSimplexCategory.map e₂ ≫ eqToHom im₁.symm
  let m₃ := eqToHom im₁ ≫ toSimplexCategory.map m₂
  haveI : Epi (eqToHom im₁.symm) := by infer_instance
  haveI : Mono (eqToHom im₁) := by infer_instance
  haveI : Epi e₃ := by
    change Epi (toSimplexCategory.map e₂ ≫ eqToHom im₁.symm)
    infer_instance
  haveI : Mono m₃ := by
    change Mono (eqToHom im₁ ≫ toSimplexCategory.map m₂)
    infer_instance
  have fac₃ : e₃ ≫ m₃ = f := by
    change (toSimplexCategory.map e₂ ≫ eqToHom im₁.symm) ≫
      (eqToHom im₁ ≫ toSimplexCategory.map m₂) = f
    rw [Category.assoc]
    rw [← Category.assoc (eqToHom im₁.symm) (eqToHom im₁)]
    simp only [eqToHom_trans, eqToHom_refl, Category.id_comp]
    exact hg
  have eq1 := SimplexCategory.image_ι_eq fac₃
  have eq2 := SimplexCategory.factorThruImage_eq fac₃
  let e₄ := eqToHom q₁ ≫ epi₁ ≫ eqToHom im₂.symm
  let m₄ := eqToHom im₂ ≫ mono₁ ≫ eqToHom q₂
  haveI : Epi (eqToHom q₁) := by infer_instance
  haveI : Epi (eqToHom im₂.symm) := by infer_instance
  haveI : Mono (eqToHom im₂) := by infer_instance
  haveI : Mono (eqToHom q₂) := by infer_instance
  haveI : Epi e₄ := by
    change Epi ((eqToHom q₁ ≫ epi₁) ≫ eqToHom im₂.symm)
    infer_instance
  haveI : Mono m₄ := by
    change Mono ((eqToHom im₂ ≫ mono₁) ≫ eqToHom q₂)
    infer_instance
  have he₄ : e₄ = epi₀ ≫ eqToHom im₂.symm := by
    simp [e₄, epi₁, Category.assoc, eqToHom_trans_assoc]
  have hm₄ : m₄ = eqToHom im₂ ≫ mono₀ := by
    simp [m₄, mono₁, Category.assoc, eqToHom_trans]
  have fac₄ : e₄ ≫ m₄ = f := by
    rw [he₄, hm₄]
    rw [Category.assoc]
    rw [← Category.assoc (eqToHom im₂.symm) (eqToHom im₂)]
    simp only [eqToHom_trans, eqToHom_refl, Category.id_comp]
    exact fac
  have eq3 := SimplexCategory.image_ι_eq fac₄
  have eq4 := SimplexCategory.factorThruImage_eq fac₄
  have hPσEq {a b : SimplexCategoryGenRel} (h : a = b) : P_σ (eqToHom h) := by
    cases h
    simpa using P_σ.id_mem a
  have hPδEq {a b : SimplexCategoryGenRel} (h : a = b) : P_δ (eqToHom h) := by
    cases h
    simpa using P_δ.id_mem a
  let e₂' : mk (z.len + k) ⟶ mk z.len :=
    eqToHom p₁.symm ≫ e₂ ≫ eqToHom eq_z₁
  let m₂' : mk z.len ⟶ mk (z.len + l) :=
    eqToHom eq_z₁.symm ≫ m₂ ≫ eqToHom p₂.symm
  have hPσ : P_σ e₂' := by
    exact P_σ.comp_mem _ _
      (hPσEq p₁.symm) (P_σ.comp_mem _ _ P_σ_e₂ (hPσEq eq_z₁))
  have hPδ : P_δ m₂' := by
    exact P_δ.comp_mem _ _
      (hPδEq eq_z₁.symm) (P_δ.comp_mem _ _ P_δ_m₂ (hPδEq p₂.symm))
  have hemap : toSimplexCategory.map e₂' = epi₁ := by
    have h := congrArg (fun e => eqToHom q₁.symm ≫ e ≫ eqToHom im₂)
      (eq2.symm.trans eq4)
    simp only [e₂', Functor.map_comp, eqToHom_map]
    change eqToHom q₁.symm ≫ toSimplexCategory.map e₂ ≫
      eqToHom (im₁.symm.trans im₂) = epi₁
    simpa only [e₃, e₄, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, Category.comp_id] using h
  have hmmap : toSimplexCategory.map m₂' = mono₁ := by
    have h := congrArg (fun m => eqToHom im₂.symm ≫ m ≫ eqToHom q₂.symm)
      (eq1.symm.trans eq3)
    simp only [m₂', Functor.map_comp, eqToHom_map]
    change eqToHom (im₂.symm.trans im₁) ≫ toSimplexCategory.map m₂ ≫
      eqToHom q₂.symm = mono₁
    simpa only [m₃, m₄, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, Category.comp_id] using h
  have heq := he₁' e₂' ⟨hPσ, hemap⟩
  have hmeq := hm₁' m₂' ⟨hPδ, hmmap⟩
  rw [fac₂]
  rw [← heq, ← hmeq]
  simp [e₂', m₂', p₁, p₂, Category.assoc]

instance : toSimplexCategory.Full where
  map_surjective {x y} f := by
    obtain ⟨a, ha, _⟩ := existsUnique_toSimplexCategory_map f
    exact ⟨a, ha⟩

instance : toSimplexCategory.Faithful where
  map_injective {x y} f g hfg := by
    obtain ⟨a, ha, u⟩ := existsUnique_toSimplexCategory_map (toSimplexCategory.map f)
    exact (u f rfl).trans (u g hfg.symm).symm

instance : toSimplexCategory.EssSurj where
  mem_essImage x := by
    let y := SimplexCategoryGenRel.mk (x.len)
    haveI : toSimplexCategory.obj y ≅ x := Iso.refl _
    apply Functor.essImage.ofIso this
    exact toSimplexCategory.obj_mem_essImage _

instance : toSimplexCategory.IsEquivalence := by
  apply Functor.IsEquivalence.mk <;> infer_instance

/-- The equivalence between `SimplexCategoryGenRel` and `SimplexCategory`. -/
noncomputable def equivSimplexCategory : SimplexCategoryGenRel ≌ SimplexCategory :=
  toSimplexCategory.asEquivalence

@[simp]
lemma equivSimplexCategory_functor_obj_mk (n : ℕ) :
    equivSimplexCategory.functor.obj (mk n) = .mk n := by
  rfl

@[simp]
lemma equivSimplexCategory_functor_map_σ (n : ℕ) (i : Fin (n + 1)) :
    equivSimplexCategory.functor.map (σ i) = SimplexCategory.σ i := by
  rfl

@[simp]
lemma equivSimplexCategory_functor_map_δ (n : ℕ) (i : Fin (n + 2)) :
    equivSimplexCategory.functor.map (δ i) = SimplexCategory.δ i := by
  rfl

/-- The inverse of equivSimplexCategory at `SimplexCategory.mk n` is isomorphism to
`SimplexCategoryGenRel.mk n`. -/
noncomputable def equivSimplexCategory_inverse_objIsoMk (n : ℕ) :
    equivSimplexCategory.inverse.obj (.mk n) ≅ mk n :=
  (equivSimplexCategory.unitIso.app (mk n)).symm

/-- The inverse of equivSimplexCategory sends the degeneracies to degeneracies, up to
conjugation by the isomorphism `equivSimplexCategory_inverse_objIsoMk`. -/
@[simp]
lemma equivSimplexCategory_inverse_map_σ (n : ℕ) (i : Fin (n + 1)) :
   (equivSimplexCategory_inverse_objIsoMk (n + 1)).inv ≫
      equivSimplexCategory.inverse.map (SimplexCategory.σ i) ≫
        (equivSimplexCategory_inverse_objIsoMk n).hom  = σ i := by
  simp only [equivSimplexCategory_inverse_objIsoMk, Iso.symm_inv, Iso.symm_hom]
  rw [← equivSimplexCategory_functor_map_σ]
  change equivSimplexCategory.unitIso.hom.app (mk (n + 1)) ≫
      (equivSimplexCategory.functor ⋙ equivSimplexCategory.inverse).map (σ i) ≫
        equivSimplexCategory.unitIso.inv.app (mk n) = σ i
  rw [← Category.assoc, ← equivSimplexCategory.unitIso.hom.naturality]
  simp

/-- The inverse of equivSimplexCategory sends the faces to faces, up to
conjugation by the isomorphism `equivSimplexCategory_inverse_objIsoMk`. -/
@[simp]
lemma equivSimplexCategory_inverse_δ (n : ℕ) (i : Fin (n + 2)):
   (equivSimplexCategory_inverse_objIsoMk n).inv ≫
      equivSimplexCategory.inverse.map (SimplexCategory.δ i) ≫
        (equivSimplexCategory_inverse_objIsoMk (n + 1)).hom  = δ i := by
  simp only [equivSimplexCategory_inverse_objIsoMk, Iso.symm_inv, Iso.symm_hom]
  rw [← equivSimplexCategory_functor_map_δ]
  change equivSimplexCategory.unitIso.hom.app (mk n) ≫
      (equivSimplexCategory.functor ⋙ equivSimplexCategory.inverse).map (δ i) ≫
        equivSimplexCategory.unitIso.inv.app (mk (n + 1)) = δ i
  rw [← Category.assoc, ← equivSimplexCategory.unitIso.hom.naturality]
  simp

end EquivalenceWithSimplexCategory

end SimplexCategoryGenRel
