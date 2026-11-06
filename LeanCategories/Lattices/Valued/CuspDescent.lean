/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

/-!
# Double cosets and the discriminant kernel (#113 item 3)

The group theory behind the descent of cusps along the discriminant action. For a normal subgroup
`K ◁ G`, a subgroup `Γ` with `K ≤ Γ`, and any subgroup `H`, the double cosets `Γ \ G / H` are the
double cosets of the images of `Γ` and `H` in `G ⧸ K`. Applied with `G = O(L)`, `K` the kernel of
the discriminant representation `ρ : O(L) → O(A_L)`, and `H` the stabilizer of a primitive isotropic
sublattice `N`, this identifies the `Γ`-orbits of the `O(L)`-translates of `N` with a double coset
space of `ρ(O(L))`.

The single hypothesis `K ≤ Γ` is what makes the descending map well defined: if `g` is replaced by
`g k` with `k ∈ K`, then `g k g⁻¹ ∈ K ⊆ Γ` absorbs the difference on the left of the double coset.
-/

@[expose] public section

open DoubleCoset

namespace LeanCategories.Lattices.Valued.CuspDescent

universe u

variable {G : Type u} [Group G]

/-- A coset `gK` determines the double coset `Γ g H` when `K ◁ G` and `K ≤ Γ`: replacing `g` by
`g k` with `k ∈ K` multiplies on the left by the conjugate `g k g⁻¹ ∈ K ≤ Γ`. -/
noncomputable def doubleCosetOfCoset (K Γ H : Subgroup G) [K.Normal] (hKΓ : K ≤ Γ) :
    G ⧸ K → DoubleCoset.Quotient (Γ : Set G) (H : Set G) :=
  Quotient.lift (fun g => DoubleCoset.mk Γ H g) (by
    intro g g' hgg'
    have hgg'' : g⁻¹ * g' ∈ K := QuotientGroup.leftRel_apply.mp hgg'
    rw [DoubleCoset.eq]
    refine ⟨g * (g⁻¹ * g') * g⁻¹,
      hKΓ (Subgroup.Normal.conj_mem inferInstance (g⁻¹ * g') hgg'' g), 1, H.one_mem, ?_⟩
    group)

/-- For `K ◁ G` and `K ≤ Γ`, the double cosets `Γ \ G / H` are the double cosets in `G ⧸ K` of the
images of `Γ` and `H`. -/
noncomputable def dosetQuotientEquiv (K Γ H : Subgroup G) [K.Normal] (hKΓ : K ≤ Γ) :
    DoubleCoset.Quotient (Γ : Set G) (H : Set G) ≃
      DoubleCoset.Quotient (Γ.map (QuotientGroup.mk' K) : Set (G ⧸ K))
        (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) where
  toFun := Quotient.lift (fun g => DoubleCoset.mk _ _ (QuotientGroup.mk' K g)) (by
    intro a b hab
    obtain ⟨γ, hγ, h, hh, rfl⟩ := (DoubleCoset.rel_iff (H := Γ) (K := H)).mp hab
    show DoubleCoset.mk _ _ (QuotientGroup.mk' K a)
      = DoubleCoset.mk _ _ (QuotientGroup.mk' K (γ * a * h))
    rw [DoubleCoset.eq]
    exact ⟨_, Subgroup.mem_map_of_mem _ hγ, _, Subgroup.mem_map_of_mem _ hh, by simp⟩)
  invFun := Quotient.lift (doubleCosetOfCoset K Γ H hKΓ) (by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ g =>
    induction y using Quotient.inductionOn with
    | _ g' =>
    obtain ⟨γ', hγ', h', hh', heq⟩ := (DoubleCoset.rel_iff
      (H := Γ.map (QuotientGroup.mk' K)) (K := H.map (QuotientGroup.mk' K))).mp hxy
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hγ'
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
    change DoubleCoset.mk Γ H g = DoubleCoset.mk Γ H g'
    rw [DoubleCoset.eq]
    have heq' : (QuotientGroup.mk' K) g' = (QuotientGroup.mk' K) (γ * g * h) := by
      rw [map_mul, map_mul]
      exact heq
    have hk : g'⁻¹ * (γ * g * h) ∈ K := QuotientGroup.eq.mp heq'
    set k := (g'⁻¹ * (γ * g * h))⁻¹ with hkdef
    have hkK : k ∈ K := K.inv_mem hk
    have hg' : g' = γ * g * h * k := by
      rw [hkdef]; group
    refine ⟨γ * (g * (h * k * h⁻¹) * g⁻¹), ?_, h, hh, ?_⟩
    · exact Γ.mul_mem hγ (hKΓ (Subgroup.Normal.conj_mem inferInstance (h * k * h⁻¹)
        (Subgroup.Normal.conj_mem inferInstance k hkK h) g))
    · rw [hg']; group)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ g => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
    induction x using Quotient.inductionOn with
    | _ g => rfl

/-- For `Γ = K` the right-hand side collapses to the coset space `(G ⧸ K) ⧸ (HK / K)`: the case
stage 1 computes, where `ρ(O(L))` acts on the discriminant form. -/
noncomputable def dosetQuotientEquivKer (K H : Subgroup G) [K.Normal] :
    DoubleCoset.Quotient (K : Set G) (H : Set G) ≃
      (G ⧸ K) ⧸ H.map (QuotientGroup.mk' K) := by
  have hbot : K.map (QuotientGroup.mk' K) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have h := dosetQuotientEquiv K K H le_rfl
  rw [hbot] at h
  rw [DoubleCoset.left_bot_eq_left_quot] at h
  exact h

end LeanCategories.Lattices.Valued.CuspDescent
