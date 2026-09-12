/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SheafPresheafComparison

/-!
# A shrinking-fibre space for the sheaf AB4* counterexample

This is the topological witness used for Weibel §3.5: one base point together with countably many
copies of `ℂˣ`. A neighbourhood of the base point contains every fibre outside a finite set.
The `n`th winding coordinate is the identity on the `n`th fibre and one on every other fibre.
-/


@[expose] public section

open CategoryTheory TopologicalSpace

namespace LeanCategories.Homological

inductive ShrinkingCStar where
  | base
  | fiber (n : ℕ) (z : ℂˣ)

namespace ShrinkingCStar

open Set

/-- An open set supported in one fibre. -/
def fiberSet (n : ℕ) (U : Set ℂˣ) : Set ShrinkingCStar :=
  {x | ∃ z, z ∈ U ∧ x = .fiber n z}

/-- A neighbourhood of the base point containing every fibre outside a finite set. -/
def tailSet (F : Finset ℕ) : Set ShrinkingCStar :=
  {x | x = .base ∨ ∃ n z, n ∉ F ∧ x = .fiber n z}

def generators : Set (Set ShrinkingCStar) :=
  {S | (∃ n U, IsOpen U ∧ S = fiberSet n U) ∨ ∃ F, S = tailSet F}

instance : TopologicalSpace ShrinkingCStar := TopologicalSpace.generateFrom generators

theorem isOpen_fiberSet (n : ℕ) {U : Set ℂˣ} (hU : IsOpen U) : IsOpen (fiberSet n U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (.inl ⟨n, U, hU, rfl⟩)

theorem isOpen_tailSet (F : Finset ℕ) : IsOpen (tailSet F) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (.inr ⟨F, rfl⟩)

@[simp] theorem base_mem_tailSet (F : Finset ℕ) : ShrinkingCStar.base ∈ tailSet F := .inl rfl

@[simp] theorem fiber_mem_tailSet_iff (F : Finset ℕ) (n : ℕ) (z : ℂˣ) :
    ShrinkingCStar.fiber n z ∈ tailSet F ↔ n ∉ F := by
  simp [tailSet]

@[simp] theorem fiber_mem_fiberSet_iff (m n : ℕ) (z : ℂˣ) (U : Set ℂˣ) :
    ShrinkingCStar.fiber n z ∈ fiberSet m U ↔ n = m ∧ z ∈ U := by
  constructor
  · rintro ⟨w, hw, h⟩
    injection h with hnm hz
    subst hnm
    subst hz
    exact ⟨rfl, hw⟩
  · rintro ⟨rfl, hz⟩
    exact ⟨z, hz, rfl⟩

/-- Every open neighbourhood of the base point contains a cofinite tail of whole fibres. -/
theorem exists_tail_subset_of_isOpen {U : Set ShrinkingCStar} (hU : IsOpen U)
    (hb : ShrinkingCStar.base ∈ U) : ∃ F : Finset ℕ, tailSet F ⊆ U := by
  change TopologicalSpace.GenerateOpen generators U at hU
  induction hU with
  | basic S hS =>
      rcases hS with hS | hS
      · rcases hS with ⟨n, V, hV, hSV⟩
        subst S
        rcases hb with ⟨z, hz, h⟩
        cases h
      · rcases hS with ⟨F, hSF⟩
        subst S
        exact ⟨F, Subset.rfl⟩
  | univ => exact ⟨∅, subset_univ _⟩
  | inter S T hS hT ihS ihT =>
      rcases ihS hb.1 with ⟨F, hF⟩
      rcases ihT hb.2 with ⟨G, hG⟩
      refine ⟨F ∪ G, ?_⟩
      intro x hx
      refine ⟨hF ?_, hG ?_⟩ <;> rcases hx with (rfl | ⟨n, z, hn, rfl⟩)
      · exact base_mem_tailSet _
      · exact (fiber_mem_tailSet_iff F n z).2 (by
          intro hnF
          exact hn (Finset.mem_union_left G hnF))
      · exact base_mem_tailSet _
      · exact (fiber_mem_tailSet_iff G n z).2 (by
          intro hnG
          exact hn (Finset.mem_union_right F hnG))
  | sUnion S hS ih =>
      rcases Set.mem_sUnion.mp hb with ⟨T, hTS, hbT⟩
      rcases ih T hTS hbT with ⟨F, hF⟩
      exact ⟨F, fun x hx => Set.mem_sUnion_of_mem (hF hx) hTS⟩

/-- A whole fibre embeds continuously into the shrinking-fibre space. -/
def fiberEmbedding (n : ℕ) : C(ℂˣ, ShrinkingCStar) :=
  ⟨ShrinkingCStar.fiber n, by
    rw [continuous_generateFrom_iff]
    intro S hS
    rcases hS with hS | hS
    · rcases hS with ⟨m, U, hU, hSU⟩
      subst S
      by_cases hnm : n = m
      · subst hnm
        simpa [fiberSet] using hU
      · have : (ShrinkingCStar.fiber n ⁻¹' fiberSet m U) = ∅ := by
          ext z
          simp [fiber_mem_fiberSet_iff, hnm]
        rw [this]
        exact isOpen_empty
    · rcases hS with ⟨F, hSF⟩
      subst S
      by_cases hnF : n ∈ F
      · have : (ShrinkingCStar.fiber n ⁻¹' tailSet F) = ∅ := by
          ext z
          simp [fiber_mem_tailSet_iff, hnF]
        rw [this]
        exact isOpen_empty
      · have : (ShrinkingCStar.fiber n ⁻¹' tailSet F) = Set.univ := by
          ext z
          simp [fiber_mem_tailSet_iff, hnF]
        rw [this]
        exact isOpen_univ⟩

/-- The `n`th winding coordinate: identity on the `n`th copy of `ℂˣ`, one elsewhere. -/
def winding (n : ℕ) : ShrinkingCStar → Additive ℂˣ
  | .base => Additive.ofMul 1
  | .fiber m z => if m = n then Additive.ofMul z else Additive.ofMul 1

theorem continuous_winding (n : ℕ) : Continuous (winding n) := by
  rw [continuous_def]
  intro U hU
  by_cases h1 : Additive.ofMul (1 : ℂˣ) ∈ U
  · change (0 : Additive ℂˣ) ∈ U at h1
    have hpre : winding n ⁻¹' U = tailSet {n} ∪
        fiberSet n (Additive.ofMul ⁻¹' U) := by
      ext x
      cases x with
      | base => simp [winding, tailSet, h1]
      | fiber m z =>
          by_cases hmn : m = n
          · subst hmn
            simp [winding, fiber_mem_tailSet_iff, fiber_mem_fiberSet_iff]
          · simp [winding, hmn, h1, fiber_mem_tailSet_iff, fiber_mem_fiberSet_iff]
    rw [hpre]
    exact (isOpen_tailSet {n}).union
      (isOpen_fiberSet n (hU.preimage continuous_ofMul))
  · have hpre : winding n ⁻¹' U = fiberSet n (Additive.ofMul ⁻¹' U) := by
      change (0 : Additive ℂˣ) ∉ U at h1
      ext x
      cases x with
      | base => simp [winding, h1, fiberSet]
      | fiber m z =>
          by_cases hmn : m = n
          · subst hmn
            simp [winding, fiber_mem_fiberSet_iff]
          · simp [winding, hmn, h1, fiber_mem_fiberSet_iff]
    rw [hpre]
    exact isOpen_fiberSet n (hU.preimage continuous_ofMul)

end ShrinkingCStar


open ShrinkingCStar

/-- Coordinatewise complex exponential on countable products. -/
noncomputable def piComplexExpAddHom : (ℕ → ℂ) →ₜ+ (ℕ → Additive ℂˣ) where
  toFun f n := complexExpAddHom (f n)
  map_zero' := by funext n; exact complexExpAddHom.map_zero
  map_add' f g := by funext n; exact complexExpAddHom.map_add (f n) (g n)
  continuous_toFun := continuous_pi fun n =>
    complexExpAddHom.continuous.comp (continuous_apply n)

/-- The simultaneous winding section on the shrinking-fibre space. -/
def simultaneousWinding : C(ShrinkingCStar, ℕ → Additive ℂˣ) :=
  ⟨fun x n => winding n x, continuous_pi continuous_winding⟩

/-- Every neighbourhood of the base point contains one whole fibre. -/
theorem exists_full_fiber_in_open (U : Opens ShrinkingCStar)
    (hb : ShrinkingCStar.base ∈ U) :
    ∃ n : ℕ, ∀ z : ℂˣ, ShrinkingCStar.fiber n z ∈ U := by
  obtain ⟨F, hF⟩ := exists_tail_subset_of_isOpen U.2 hb
  let G : Finset ℕ := insert 0 F
  have hG : G.Nonempty := ⟨0, Finset.mem_insert_self 0 F⟩
  let n := G.max' hG + 1
  have hnG : n ∉ G := by
    intro hn
    have hle : n ≤ G.max' hG := Finset.le_max' G n hn
    exact Nat.not_succ_le_self (G.max' hG) hle
  have hnF : n ∉ F := by
    intro hn
    exact hnG (Finset.mem_insert_of_mem hn)
  refine ⟨n, fun z => hF ?_⟩
  exact (fiber_mem_tailSet_iff F n z).2 hnF

/-- No neighbourhood of the base point admits continuous logarithms of all winding coordinates
simultaneously. -/
theorem no_simultaneous_log_on_neighborhood (U : Opens ShrinkingCStar)
    (hb : ShrinkingCStar.base ∈ U) :
    ¬ ∃ s : C(U, ℕ → ℂ),
      ∀ x : U, piComplexExpAddHom (s x) = simultaneousWinding x.1 := by
  rintro ⟨s, hs⟩
  obtain ⟨n, hn⟩ := exists_full_fiber_in_open U hb
  let j : C(ℂˣ, U) :=
    ⟨fun z => ⟨ShrinkingCStar.fiber n z, hn z⟩,
      (fiberEmbedding n).continuous.subtype_mk _⟩
  let l : C(ℂˣ, ℂ) :=
    ⟨fun z => s (j z) n,
      (continuous_apply n).comp (s.continuous.comp j.continuous)⟩
  apply noContinuousGlobalLog
  refine ⟨l, ?_⟩
  intro z
  have h := congrFun (hs (j z)) n
  change complexExpAddHom (s (j z) n) = winding n (j z).1 at h
  have hj : (j z).1 = ShrinkingCStar.fiber n z := rfl
  rw [hj] at h
  simp only [winding] at h
  change complexExpAddHom (l z) = Additive.ofMul z
  simpa [l, j] using h

end LeanCategories.Homological
