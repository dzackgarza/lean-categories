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

## Trap: `ρ.ker` versus `stableOrthogonalGroup hL`

`OrthogonalGroup.stableOrthogonalGroup hL` is *defined* to be
`MonoidHom.ker (OrthogonalGroup.discriminantRepresentation hL)`, so the two subgroups are
interchangeable by `rfl` in any *term*. They are **not** interchangeable in a *statement*.

`QuotientGroup.mk' (OrthogonalGroup.stableOrthogonalGroup hL)` does not elaborate: `mk'` needs a
`Normal` instance, and `MonoidHom.normal_ker` is found only when the subgroup is syntactically a
kernel. `letI`/`haveI` inside a proof comes too late, because the statement is elaborated first.
Inside a *definition* the `letI` works, which is why `discriminantRangeImage` elaborates and a new
lemma mentioning `mk' (stableOrthogonalGroup hL)` in its type does not.

Consequences, both exercised above:

* state the triangle identity at `ρ.ker`, not at `stableOrthogonalGroup hL`
  (`quotientKerEquivRange_comp_mk'_ker`);
* when a statement must move between the two spellings, close it by definitional unfolding
  (`exact`), not by `rw`: `Subgroup.map_map` will not fire on a `mk' (stableOrthogonalGroup hL)`
  argument, and the implying goal is not even type-correct at `implicit` transparency.
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

namespace LeanCategories.Lattices.Valued.CuspDescent

universe u

variable {G : Type u} [Group G] {G' : Type u} [Group G']

/-- A group isomorphism carries the double cosets of `A` and `B` to the double cosets of their
images. -/
noncomputable def DoubleCoset.quotientMulEquiv (e : G ≃* G') (A B : Subgroup G) :
    DoubleCoset.Quotient (A : Set G) (B : Set G) ≃
      DoubleCoset.Quotient (A.map e.toMonoidHom : Set G') (B.map e.toMonoidHom : Set G') where
  toFun := Quotient.map (e : G → G') (by
    intro a b hab
    obtain ⟨γ, hγ, h, hh, rfl⟩ := (DoubleCoset.rel_iff (H := A) (K := B)).mp hab
    exact (DoubleCoset.rel_iff (H := A.map e.toMonoidHom) (K := B.map e.toMonoidHom)).mpr
      ⟨e γ, Subgroup.mem_map_of_mem _ hγ, e h, Subgroup.mem_map_of_mem _ hh, by simp⟩)
  invFun := Quotient.map (e.symm : G' → G) (by
    intro a b hab
    obtain ⟨γ, hγ, h, hh, rfl⟩ := (DoubleCoset.rel_iff
      (H := A.map e.toMonoidHom) (K := B.map e.toMonoidHom)).mp hab
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh
    exact (DoubleCoset.rel_iff (H := A) (K := B)).mpr
      ⟨γ₀, hγ₀, h₀, hh₀, by simp⟩)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ g =>
      simp only [Quotient.map_mk, MulEquiv.symm_apply_apply]
      rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ g =>
      simp only [Quotient.map_mk, MulEquiv.apply_symm_apply]
      rfl

end LeanCategories.Lattices.Valued.CuspDescent

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] {L : IntegralLatticeCat R}

/-- The image of a subgroup of `O(L)` in the discriminant range `ρ(O(L))`, through `G ⧸ ker ρ`. -/
noncomputable def discriminantRangeImage [IsDomain R] (hL : IsFractionFieldPerfect R L)
    (H : Subgroup (OrthogonalGroup L)) :
    Subgroup (OrthogonalGroup.discriminantRepresentation hL).range :=
  letI : (OrthogonalGroup.stableOrthogonalGroup hL).Normal := MonoidHom.normal_ker _
  (H.map (QuotientGroup.mk' (OrthogonalGroup.stableOrthogonalGroup hL))).map
    (QuotientGroup.quotientKerEquivRange
      (OrthogonalGroup.discriminantRepresentation hL)).toMonoidHom

/-- The `Γ`-orbits of primitive isotropic sublattices lying over the `O(L)`-orbit of `N` are the
double cosets of the images of `Γ` and of the stabilizer of `N` in the discriminant range
`ρ(O(L))`, for `Γ` containing the stable orthogonal group `ker ρ`. -/
noncomputable def cuspOrbitsEquivDoubleCosetsDiscriminant [IsDomain R]
    (hL : IsFractionFieldPerfect R L) (Γ : FiniteIndexSubgroup L)
    (hKΓ : OrthogonalGroup.stableOrthogonalGroup hL ≤ Γ.toSubgroup) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    {c : CuspOrbits L Γ k //
        ∃ v ∈ MulAction.orbit (OrthogonalGroup L) N, CuspOrbits.mk Γ v = c} ≃
      DoubleCoset.Quotient
        (discriminantRangeImage hL Γ.toSubgroup :
          Set (OrthogonalGroup.discriminantRepresentation hL).range)
        (discriminantRangeImage hL (MulAction.stabilizer (OrthogonalGroup L) N) :
          Set (OrthogonalGroup.discriminantRepresentation hL).range) := by
  haveI : (OrthogonalGroup.stableOrthogonalGroup hL).Normal := MonoidHom.normal_ker _
  exact ((dosetQuotientOrbit Γ N).symm.trans
    (CuspDescent.dosetQuotientEquiv (OrthogonalGroup.stableOrthogonalGroup hL) Γ.toSubgroup
      (MulAction.stabilizer (OrthogonalGroup L) N) hKΓ)).trans
    (CuspDescent.DoubleCoset.quotientMulEquiv
      (QuotientGroup.quotientKerEquivRange (OrthogonalGroup.discriminantRepresentation hL)) _ _)

/-- The quotient map through the kernel followed by the identification with the range is the range
restriction of `ρ`. -/
theorem quotientKerEquivRange_comp_mk'_ker [IsDomain R]
    (hL : IsFractionFieldPerfect R L) :
    (QuotientGroup.quotientKerEquivRange
        (OrthogonalGroup.discriminantRepresentation hL)).toMonoidHom.comp
      (QuotientGroup.mk' (OrthogonalGroup.discriminantRepresentation hL).ker) =
      (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict := by
  ext x
  simp only [MonoidHom.comp_apply, QuotientGroup.quotientKerEquivRange,
    QuotientGroup.rangeKerLift, MonoidHom.coe_rangeRestrict]
  rfl

/-- The image of a subgroup of `O(L)` in the discriminant range is its image under the range
restriction of `ρ`. -/
theorem discriminantRangeImage_eq_map_rangeRestrict [IsDomain R]
    (hL : IsFractionFieldPerfect R L) (H : Subgroup (OrthogonalGroup L)) :
    discriminantRangeImage hL H =
      H.map (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict := by
  rw [discriminantRangeImage]
  have h : Subgroup.map
      (QuotientGroup.quotientKerEquivRange
        (OrthogonalGroup.discriminantRepresentation hL)).toMonoidHom
      (Subgroup.map (QuotientGroup.mk' (OrthogonalGroup.discriminantRepresentation hL).ker) H) =
      Subgroup.map (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict H := by
    rw [Subgroup.map_map, quotientKerEquivRange_comp_mk'_ker hL]
  exact h


/-- The same orbit equivalence with the target written as the double cosets of the images of `Γ` and
of the stabilizer of `N` under `ρ` itself, which is the statement of prop:descent-fibre. -/
noncomputable def cuspOrbitsEquivDoubleCosetsDiscriminantRange [IsDomain R]
    (hL : IsFractionFieldPerfect R L) (Γ : FiniteIndexSubgroup L)
    (hKΓ : OrthogonalGroup.stableOrthogonalGroup hL ≤ Γ.toSubgroup) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    {c : CuspOrbits L Γ k //
        ∃ v ∈ MulAction.orbit (OrthogonalGroup L) N, CuspOrbits.mk Γ v = c} ≃
      DoubleCoset.Quotient
        (Γ.toSubgroup.map (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict :
          Set (OrthogonalGroup.discriminantRepresentation hL).range)
        ((MulAction.stabilizer (OrthogonalGroup L) N).map
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict :
          Set (OrthogonalGroup.discriminantRepresentation hL).range) :=
  (cuspOrbitsEquivDoubleCosetsDiscriminant hL Γ hKΓ N).trans
    (Equiv.cast (by
      rw [discriminantRangeImage_eq_map_rangeRestrict hL,
        discriminantRangeImage_eq_map_rangeRestrict hL]))

end LeanCategories.Lattices.Valued