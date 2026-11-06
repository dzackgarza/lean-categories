/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic
public import LeanCategories.Lattices.Valued.Cusps

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

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] {L : IntegralLatticeCat R}

/-- A `Γ`-translate lies in the same `Γ`-orbit. -/
theorem CuspOrbits.mk_smul (Γ : FiniteIndexSubgroup L) {k : ℕ} (γ : ↥Γ.toSubgroup)
    (X : PrimitiveIsotropic L k) : CuspOrbits.mk Γ (γ • X) = CuspOrbits.mk Γ X :=
  Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩)

/-- A primitive isotropic sublattice in the `O(L)`-orbit of `N` determines the double coset of any
`g` with `g • N = v`; the choice is `Classical.choose` on the orbit membership. -/
noncomputable def dosetOfOrbit (Γ : FiniteIndexSubgroup L) {k : ℕ} (N : PrimitiveIsotropic L k)
    (v : {v // v ∈ MulAction.orbit (OrthogonalGroup L) N}) :
    DoubleCoset.Quotient (Γ.toSubgroup : Set (OrthogonalGroup L))
      (MulAction.stabilizer (OrthogonalGroup L) N : Set (OrthogonalGroup L)) :=
  DoubleCoset.mk _ _ (Classical.choose (MulAction.mem_orbit_iff.mp v.2))

/-- The double coset `Γ g H` gives the `Γ`-class of `g • N`. -/
noncomputable def cuspOrbitOfDoset (Γ : FiniteIndexSubgroup L) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    DoubleCoset.Quotient (Γ.toSubgroup : Set (OrthogonalGroup L))
        (MulAction.stabilizer (OrthogonalGroup L) N : Set (OrthogonalGroup L)) →
      {c : CuspOrbits L Γ k //
        ∃ v ∈ MulAction.orbit (OrthogonalGroup L) N, CuspOrbits.mk Γ v = c} :=
  Quotient.lift
    (fun g => ⟨CuspOrbits.mk Γ (g • N),
      ⟨g • N, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩, rfl⟩⟩)
    (by
      intro a b hab
      obtain ⟨γ, hγ, h, hh, rfl⟩ := (DoubleCoset.rel_iff
        (H := Γ.toSubgroup)
        (K := MulAction.stabilizer (OrthogonalGroup L) N)).mp hab
      simp only [Subtype.mk.injEq]
      rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp hh]
      exact (CuspOrbits.mk_smul Γ ⟨γ, hγ⟩ (a • N)).symm)

theorem cuspOrbitOfDoset_injective (Γ : FiniteIndexSubgroup L) {k : ℕ}
    (N : PrimitiveIsotropic L k) : Function.Injective (cuspOrbitOfDoset Γ N) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ g =>
  induction y using Quotient.inductionOn with
  | _ g' =>
  have h1 : CuspOrbits.mk Γ (g • N) = CuspOrbits.mk Γ (g' • N) := by
    have h := congrArg Subtype.val hxy
    change CuspOrbits.mk Γ (g • N) = CuspOrbits.mk Γ (g' • N) at h
    exact h
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact h1))
  have hγ' : (γ : OrthogonalGroup L) • (g' • N) = g • N := hγ
  have hstab : (g⁻¹ * (γ : OrthogonalGroup L) * g') ∈
      MulAction.stabilizer (OrthogonalGroup L) N := by
    rw [MulAction.mem_stabilizer_iff]
    have hstep : (g⁻¹ * (γ : OrthogonalGroup L) * g') • N =
        g⁻¹ • ((γ : OrthogonalGroup L) • (g' • N)) := by
      simp [mul_smul]
    rw [hstep, hγ', inv_smul_smul]
  refine (DoubleCoset.eq (Γ.toSubgroup)
    (MulAction.stabilizer (OrthogonalGroup L) N) g g').mpr
    ⟨(γ : OrthogonalGroup L)⁻¹, Γ.toSubgroup.inv_mem γ.2, g⁻¹ * (γ : OrthogonalGroup L) * g',
      hstab, by group⟩

theorem cuspOrbitOfDoset_surjective (Γ : FiniteIndexSubgroup L) {k : ℕ}
    (N : PrimitiveIsotropic L k) : Function.Surjective (cuspOrbitOfDoset Γ N) := by
  intro p
  obtain ⟨c, hc⟩ := p
  obtain ⟨v, hv, hvc⟩ := hc
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hv
  exact ⟨DoubleCoset.mk _ _ g, by
    apply Subtype.ext
    change CuspOrbits.mk Γ (g • N) = c
    rw [hg, hvc]⟩

/-- The `Γ`-orbits of primitive isotropic sublattices in the `O(L)`-orbit of `N` are the double
cosets of `Γ` and the stabilizer of `N`. -/
noncomputable def dosetQuotientOrbit (Γ : FiniteIndexSubgroup L) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    DoubleCoset.Quotient (Γ.toSubgroup : Set (OrthogonalGroup L))
        (MulAction.stabilizer (OrthogonalGroup L) N : Set (OrthogonalGroup L)) ≃
      {c : CuspOrbits L Γ k //
        ∃ v ∈ MulAction.orbit (OrthogonalGroup L) N, CuspOrbits.mk Γ v = c} :=
  Equiv.ofBijective _ ⟨cuspOrbitOfDoset_injective Γ N, cuspOrbitOfDoset_surjective Γ N⟩

end LeanCategories.Lattices.Valued
