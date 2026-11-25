/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantAction
public import LeanCategories.Lattices.Valued.CuspDescent
public import LeanCategories.Modules.Bilinear.Valued.Witt

/-!
# The isotropic subgroup `J_N = (N_ℚ ∩ L^∨)/N` of the discriminant form (#113 item 3)

For a primitive isotropic sublattice `N ⊆ L`, the subgroup of `A_L` carried by `N` is
`J_N = (N_ℚ ∩ L^∨)/N`: the rational span of `N` intersected with the dual lattice, modulo `N`. It is
not the dual of `N` — `N` is isotropic, so everything in `N_ℚ` pairs to zero with `N` and that dual
is all of `N_ℚ`.

The construction here avoids fraction-field scalars. Everything is an `R`-module: the dual lattice is
`metricDual R L`, the image `N'` of `N` is `N.toSubmodule.map (toMetricDual R L)`, and the rational
span intersected with `L^∨` is the *saturation* of `N'`,

`{x ∈ L^∨ | ∃ r ≠ 0, r • x ∈ N'}`,

which is `Sublattice.saturation N'` — the same construction that gives primitive closure in
`Sublattice.lean`, and its membership lemma `mem_saturation_iff` is what the isotropy argument
consumes. `metricDualToDiscriminant` then carries the saturation into `A_L = L.obj.defect`, and the
image is `J_N`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R] {L : IntegralLatticeCat R}

/-- The image of the primitive isotropic sublattice `N` in the dual lattice `L^∨`. -/
noncomputable abbrev metricDualImage {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R ↥(metricDual R L) :=
  N.toSubmodule.map (toMetricDual R L)

/-- `N_ℚ ∩ L^∨`: the saturation of the image of `N` in the dual lattice, i.e. the elements killed
into that image by a nonzero scalar. -/
noncomputable abbrev metricDualSaturation {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R ↥(metricDual R L) :=
  saturation (M := ↥(metricDual R L)) (metricDualImage N)

/-- `J_N = (N_ℚ ∩ L^∨)/N`, as a subgroup of the discriminant module `A_L`. -/
noncomputable abbrev isotropicSubgroup {k : ℕ} (N : PrimitiveIsotropic L k) :
    Submodule R L.obj.defect :=
  (metricDualSaturation N).map (metricDualToDiscriminant R L)

theorem discriminantBilinMap_eq_zero_of_mem_isotropicSubgroup
    (hL : IsFractionFieldPerfect R L) {k : ℕ} (N : PrimitiveIsotropic L k)
    {u v : L.obj.defect} (hu : u ∈ isotropicSubgroup N) (hv : v ∈ isotropicSubgroup N) :
    discriminantBilinMap R L hL u v = 0 := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hu
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
  rw [show discriminantBilinMap R L hL (metricDualToDiscriminant R L x)
        (metricDualToDiscriminant R L y) =
      fractionValueProjection R (rationalizedForm R L (↑x) (↑y)) from
    discriminant_pairing_metricDualToDiscriminant R hL x y]
  obtain ⟨r, hr, hrx⟩ := (mem_saturation_iff (metricDualImage N) x).mp hx
  obtain ⟨s, hs, hsy⟩ := (mem_saturation_iff (metricDualImage N) y).mp hy
  obtain ⟨a', ha', hra'⟩ := Submodule.mem_map.mp hrx
  obtain ⟨b', hb', hsb'⟩ := Submodule.mem_map.mp hsy
  have hxr : r • (↑x : RationalSpan R L) = ↑(toMetricDual R L a') := by
    rw [← Submodule.coe_smul, ← hra']
  have hys : s • (↑y : RationalSpan R L) = ↑(toMetricDual R L b') := by
    rw [← Submodule.coe_smul, ← hsb']
  have hpair : rationalizedForm R L (↑(toMetricDual R L a')) (↑(toMetricDual R L b')) = 0 := by
    rw [rationalizedForm_toMetricDual, ← IntegralLatticeCat.asBilinForm_apply,
      N.isotropic a' ha' b' hb', map_zero]
  have hfac : rationalizedForm R L (r • (↑x : RationalSpan R L)) (s • (↑y : RationalSpan R L)) =
      algebraMap R (FractionRing R) r * (algebraMap R (FractionRing R) s *
        rationalizedForm R L (↑x) (↑y)) := by
    rw [← IsScalarTower.algebraMap_smul (A := FractionRing R) r (↑x : RationalSpan R L),
      ← IsScalarTower.algebraMap_smul (A := FractionRing R) s (↑y : RationalSpan R L),
      LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_left]
    ring
  rw [hxr, hys, hpair] at hfac
  have hne : algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) s ≠ 0 := by
    rw [← map_mul]
    intro h0
    exact mul_ne_zero hr hs (IsFractionRing.injective R (FractionRing R) (by rw [h0, map_zero]))
  have hzero : rationalizedForm R L (↑x) (↑y) = 0 := by
    have h0 : algebraMap R (FractionRing R) r * (algebraMap R (FractionRing R) s *
        rationalizedForm R L (↑x) (↑y)) = 0 := hfac.symm
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (fun h1 => hr (IsFractionRing.injective R (FractionRing R)
        (by rw [h1, map_zero])))
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (fun h1 => hs (IsFractionRing.injective R (FractionRing R)
          (by rw [h1, map_zero])))
      · exact h'
  rw [hzero, map_zero]

/-- In `L^∨`, the saturation of `N` meets the kernel of the projection to `A_L` exactly along the
image of `N` itself, because the kernel is `toMetricDual`-of `L` and `N` is primitive. -/
theorem ker_inf_saturation (hL : IsFractionFieldPerfect R L) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    LinearMap.ker (metricDualToDiscriminant R L) ⊓ metricDualSaturation N = metricDualImage N := by
  rw [ker_metricDualToDiscriminant R L hL]
  apply le_antisymm
  · rintro x ⟨⟨a, rfl⟩, hx⟩
    obtain ⟨r, hr, hrx⟩ := (mem_saturation_iff (metricDualImage N) (toMetricDual R L a)).mp hx
    obtain ⟨b, hb, hrb⟩ := Submodule.mem_map.mp hrx
    have hb' : b = r • a := by
      apply toMetricDual_injective
      rw [hrb, map_smul]
    have ha' : r • a ∈ N.toSubmodule := hb' ▸ hb
    have ha : a ∈ saturation (M := L.obj.carrier) N.toSubmodule := by
      rw [mem_saturation_iff]
      exact ⟨r, hr, ha'⟩
    rw [(isPrimitiveSubmodule_iff_saturation_eq N.toSubmodule).mp N.primitive] at ha
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    refine ⟨⟨a, rfl⟩, le_saturation (M := ↥(metricDual R L)) (metricDualImage N) hx⟩

theorem actOnMetricDual_toMetricDual (hL : IsFractionFieldPerfect R L)
    (g : OrthogonalGroup L) (x : L.obj.carrier) :
    OrthogonalGroup.actOnMetricDual g hL (toMetricDual R L x) = toMetricDual R L (g.1 x) := by
  apply Subtype.ext
  rw [OrthogonalGroup.actOnMetricDual_coe]
  show OrthogonalGroup.actOnRationalSpan g (↑(toMetricDual R L x) : RationalSpan R L) =
    ↑(toMetricDual R L (g.1 x))
  have hx : (↑(toMetricDual R L x) : RationalSpan R L) = toRationalSpan R L x := rfl
  rw [hx]
  simp [OrthogonalGroup.actOnRationalSpan, toRationalSpan]
  rfl

/-- The dual action and mapping along a submodule commute: `g • (N.map toMetricDual) =
(g • N).map toMetricDual`, because `actOnMetricDual` is the dual action of the isometry on the
metric dual and `toMetricDual` is equivariant. -/
theorem map_toMetricDual_smul (hL : IsFractionFieldPerfect R L) (g : OrthogonalGroup L)
    {k : ℕ} (N : PrimitiveIsotropic L k) :
    (N.toSubmodule.map (toMetricDual R L)).map (OrthogonalGroup.actOnMetricDual g hL).toLinearMap =
      (g • N).toSubmodule.map (toMetricDual R L) := by
  have hcomp : (OrthogonalGroup.actOnMetricDual g hL).toLinearMap.comp (toMetricDual R L) =
      (toMetricDual R L).comp (g.1.toLinearMap) := by
    ext x
    simpa using actOnMetricDual_toMetricDual hL g x
  calc
    _ = N.toSubmodule.map ((OrthogonalGroup.actOnMetricDual g hL).toLinearMap.comp
        (toMetricDual R L)) := (Submodule.map_comp _ _ _).symm
    _ = N.toSubmodule.map ((toMetricDual R L).comp (g.1.toLinearMap)) := by rw [hcomp]
    _ = (g • N).toSubmodule.map (toMetricDual R L) := Submodule.map_comp _ _ _

/-- `saturation` commutes with mappings by a linear equivalence: membership is the same nonzero
scalar condition on either side. -/
theorem saturation_map_equiv {M M' : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') (P : Submodule R M) :
    (saturation P).map (e : M →ₗ[R] M') = saturation (P.map (e : M →ₗ[R] M')) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hay⟩ := (mem_saturation_iff (M := M) P y).mp hy
    refine (mem_saturation_iff (M := M') (P.map (e : M →ₗ[R] M')) ((e : M →ₗ[R] M') y)).mpr ⟨a, ha, ?_⟩
    have hmem : e (a • y) ∈ Submodule.map (e : M →ₗ[R] M') P :=
      Submodule.mem_map_of_mem hay
    rw [← map_smul]
    exact hmem
  · intro x hx
    obtain ⟨a, ha, hax⟩ := (mem_saturation_iff (M := M') (P.map (e : M →ₗ[R] M')) x).mp hx
    obtain ⟨z, hz, hez⟩ := Submodule.mem_map.mp hax
    have hz' : a • e.symm x = z := by
      calc a • e.symm x = e.symm (a • x) := (map_smul e.symm a x).symm
        _ = z := by rw [← hez]; exact e.symm_apply_apply z
    have hx' : e.symm x ∈ saturation P :=
      (mem_saturation_iff (M := M) P (e.symm x)).mpr ⟨a, ha, by rw [hz']; exact hz⟩
    exact (Submodule.mem_map (f := (e : M →ₗ[R] M')) (p := saturation P)).mpr
      ⟨e.symm x, hx', e.apply_symm_apply x⟩

/-- `J_N` is equivariant for the isometry: `isotropicSubgroup (g • N) = g • J_N`. The three
transport steps are `map_toMetricDual_smul` for the image, `saturation_map_equiv` for the
saturation itself, and `OrthogonalGroup.metricDualToDiscriminant_actOnMetricDual` for the
projection to `A_L`. -/
theorem isotropicSubgroup_smul (hL : IsFractionFieldPerfect R L)
    (g : OrthogonalGroup L) {k : ℕ} (N : PrimitiveIsotropic L k) :
    isotropicSubgroup (g • N) =
      (isotropicSubgroup N).map (OrthogonalGroup.actOnDefect g).toLinearMap := by
  calc
    isotropicSubgroup (g • N) =
        (saturation (M := ↥(metricDual R L)) ((N.toSubmodule.map (toMetricDual R L)).map
            (OrthogonalGroup.actOnMetricDual g hL).toLinearMap)).map
          (metricDualToDiscriminant R L) := by
      rw [map_toMetricDual_smul hL g N]
    _ = ((metricDualSaturation N).map
        (OrthogonalGroup.actOnMetricDual g hL).toLinearMap).map
        (metricDualToDiscriminant R L) := by
      have h := saturation_map_equiv (M := ↥(metricDual R L)) (M' := ↥(metricDual R L))
        (e := OrthogonalGroup.actOnMetricDual g hL)
        (P := N.toSubmodule.map (toMetricDual R L))
      exact congrArg (Submodule.map (metricDualToDiscriminant R L)) h.symm
    _ = (isotropicSubgroup N).map (OrthogonalGroup.actOnDefect g).toLinearMap := by
        have hmap : (metricDualToDiscriminant R L).comp
            (OrthogonalGroup.actOnMetricDual g hL).toLinearMap =
          (OrthogonalGroup.actOnDefect g).toLinearMap.comp (metricDualToDiscriminant R L) := by
          ext x
          exact OrthogonalGroup.metricDualToDiscriminant_actOnMetricDual g hL x
        rw [← Submodule.map_comp, ← Submodule.map_comp, hmap]

theorem isotropicSubgroup_smul_of_mem_stable (hL : IsFractionFieldPerfect R L)
    {k : ℕ} (N : PrimitiveIsotropic L k) (γ : OrthogonalGroup L)
    (hγ : γ ∈ OrthogonalGroup.stableOrthogonalGroup hL) :
    isotropicSubgroup (γ • N) = isotropicSubgroup N := by
  have hact : OrthogonalGroup.actOnDiscriminantForm γ hL = 1 := hγ
  have heq : OrthogonalGroup.actOnDefect γ = 1 := congrArg (fun z => z.1) hact
  rw [isotropicSubgroup_smul hL γ N, heq]
  exact Submodule.map_id _

/-- The class of a primitive isotropic sublattice, read on the `K`-orbit set: well-defined because
ker ρ preserves every `J_N`. -/
noncomputable def CuspOrbits.isotropicSubgroup
    (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) {k : ℕ} :
    let Γ : FiniteIndexSubgroup L := ⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩
    CuspOrbits L Γ k → Submodule R L.obj.defect := by
  intro Γ
  exact Quotient.lift (fun N : PrimitiveIsotropic L k => LeanCategories.Lattices.Valued.isotropicSubgroup N) (by
    intro a b hrel
    obtain ⟨γ, hγ⟩ := hrel
    have hsub : (γ : OrthogonalGroup L) • b = a := hγ
    rw [← hsub]
    exact isotropicSubgroup_smul_of_mem_stable hL b γ γ.2)

noncomputable instance parentDefect (hL : IsFractionFieldPerfect R L) :
    MulAction (BilinModuleCat.OrthogonalGroup (discriminantBilinObject R L hL))
      (Submodule R L.obj.defect) :=
  BilinModuleCat.OrthogonalGroup.submoduleMulAction (discriminantBilinObject R L hL)

noncomputable instance rangeDefect (hL : IsFractionFieldPerfect R L) :
    MulAction ↥(OrthogonalGroup.discriminantRepresentation hL).range
      (Submodule R L.obj.defect) :=
  MulAction.compHom
    (M := BilinModuleCat.OrthogonalGroup (discriminantBilinObject R L hL))
    (Submodule R L.obj.defect)
    (show ↥(OrthogonalGroup.discriminantRepresentation hL).range →*
      BilinModuleCat.OrthogonalGroup (discriminantBilinObject R L hL) from
      Subgroup.subtype _)

/-- The discriminant range acts on the discriminant module itself, by restriction of scalars. The
submodule action above is used for isotropic subgroups; this one is what the stabilizer of a
*discriminant class* needs. The carrier of the discriminant bilinear object is definitionally `A_L`
but type class search does not identify it with `L.obj.defect`, so the action is written out at
`L.obj.defect`, which is where `discriminantClass` and `actOnDefect` live. -/
noncomputable instance rangeDefectPoint (hL : IsFractionFieldPerfect R L) :
    MulAction ↥(OrthogonalGroup.discriminantRepresentation hL).range L.obj.defect where
  smul x c := (x.1.1 : (discriminantBilinObject R L hL).carrier ≃ₗ[R]
    (discriminantBilinObject R L hL).carrier) c
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem CuspOrbits.isotropicSubgroup_cuspOrbitOfDoset
    (hL : IsFractionFieldPerfect R L) (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex)
    {k : ℕ} (N : PrimitiveIsotropic L k)
    (g : OrthogonalGroup L) :
    CuspOrbits.isotropicSubgroup (k := k) hL hΓ
      (cuspOrbitOfDoset (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
        FiniteIndexSubgroup L) N
        (DoubleCoset.mk (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L).toSubgroup
          (MulAction.stabilizer (OrthogonalGroup L) N) g)) =
      (LeanCategories.Lattices.Valued.isotropicSubgroup N).map
        (OrthogonalGroup.actOnDefect g).toLinearMap := by
  simp only [CuspOrbits.isotropicSubgroup, Quotient.lift]
  exact isotropicSubgroup_smul hL g N


/-- The class determined by a lift is the class of `N` exactly when the lift acts trivially on the
isotropic subgroup. -/
theorem cuspOrbits_class_eq_iff_stabilizer
    (hL : IsFractionFieldPerfect R L) (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex)
    {k : ℕ} (N : PrimitiveIsotropic L k) (g : OrthogonalGroup L) :
    CuspOrbits.isotropicSubgroup (k := k) hL hΓ
        (cuspOrbitOfDoset (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L) N
          (DoubleCoset.mk (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
            FiniteIndexSubgroup L).toSubgroup
            (MulAction.stabilizer (OrthogonalGroup L) N) g)) =
          (isotropicSubgroup N : Submodule R L.obj.defect) ↔
      (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g ∈
        MulAction.stabilizer
          ↥(OrthogonalGroup.discriminantRepresentation hL).range
          (isotropicSubgroup N) := by
  rw [CuspOrbits.isotropicSubgroup_cuspOrbitOfDoset hL hΓ N g]
  exact Iff.rfl

/-- Elements of the stabilizer of `N` lift into the stabilizer of `J_N`. -/
theorem stabilizerMap_le (hL : IsFractionFieldPerfect R L) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    (MulAction.stabilizer (OrthogonalGroup L) N).map
        (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict ≤
      MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (isotropicSubgroup N) := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
  rw [MulAction.mem_stabilizer_iff]
  change (isotropicSubgroup N).map (OrthogonalGroup.actOnDefect g).toLinearMap =
    isotropicSubgroup N
  rw [← isotropicSubgroup_smul hL g N, (MulAction.mem_stabilizer_iff).mp hg]

/-- The predicate `g ∈ K` on left cosets of a smaller subgroup, well-defined when `H ≤ K`. -/
def inCoset {G : Type u} [Group G] (H K : Subgroup G) (hHK : H ≤ K) : G ⧸ H → Prop :=
  Quotient.lift (fun g : G => g ∈ K) (by
    intro a b hrel
    have hmem : a⁻¹ * b ∈ K := hHK ((QuotientGroup.leftRel_apply).mp hrel)
    apply propext
    constructor
    · intro ha
      have hmem' := K.mul_mem ha hmem
      convert hmem' using 1; group
    · intro hb
      have hmem' := K.mul_mem hb (K.inv_mem hmem)
      convert hmem' using 1; group)

lemma inCoset_mk {G : Type u} [Group G] (H K : Subgroup G) (hHK : H ≤ K) (g : G) :
    inCoset H K hHK (QuotientGroup.mk g) = (g ∈ K) := by rfl

/-- The cosets of a subgroup `H` inside its own stabilizer are the left cosets by `H` in `K`. -/
noncomputable def cosetInEquiv {G : Type u} [Group G] (H K : Subgroup G) (hHK : H ≤ K) :
    {x : G ⧸ H // inCoset H K hHK x} ≃ K ⧸ H.subgroupOf K := by
  let f : K ⧸ H.subgroupOf K → {x : G ⧸ H // inCoset H K hHK x} :=
    fun y => ⟨Quotient.map (fun g : K => g.1) (fun a b h => (QuotientGroup.leftRel_apply).mpr
        (Subgroup.mem_subgroupOf.mp ((QuotientGroup.leftRel_apply).mp h))) y, by
      induction y using Quotient.inductionOn with
      | _ g => exact g.2⟩
  apply Equiv.symm (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
    apply Quotient.eq.mpr
    have h := congrArg Subtype.val hxy
    simp only [f, Quotient.map_mk] at h
    apply (QuotientGroup.leftRel_apply).mpr
      (Subgroup.mem_subgroupOf.mpr ((QuotientGroup.leftRel_apply).mp (Quotient.exact h)))
  · intro x
    obtain ⟨z, hz⟩ := x
    induction z using Quotient.inductionOn with
    | _ g =>
    have hg : g ∈ K := hz
    refine ⟨QuotientGroup.mk ⟨g, hg⟩, Subtype.ext ?_⟩
    rfl

abbrev StableFibre (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) (k : ℕ)
    (N : PrimitiveIsotropic L k) :=
  {a : {c : CuspOrbits L (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
        FiniteIndexSubgroup L) k //
      ∃ v ∈ MulAction.orbit (OrthogonalGroup L) N,
          CuspOrbits.mk (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
            FiniteIndexSubgroup L) v = c} //
    CuspOrbits.isotropicSubgroup hL hΓ a.1 = isotropicSubgroup N}

/-- The same fibre on the raw double cosets. -/
abbrev DosetFibre (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) (k : ℕ)
    (N : PrimitiveIsotropic L k) :=
  {d : DoubleCoset.Quotient
      ((⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
        FiniteIndexSubgroup L).toSubgroup : Set (OrthogonalGroup L))
      (MulAction.stabilizer (OrthogonalGroup L) N : Set (OrthogonalGroup L)) //
    CuspOrbits.isotropicSubgroup hL hΓ
      (LeanCategories.Lattices.Valued.cuspOrbitOfDoset
        (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L) N d).1 = isotropicSubgroup N}

variable (hL : IsFractionFieldPerfect R L)
variable (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex)

noncomputable def stableFibreEquivDosetFibre :
    {a : {c : CuspOrbits L (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L) k //
          ∃ v ∈ MulAction.orbit (OrthogonalGroup L) N,
            CuspOrbits.mk (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
              FiniteIndexSubgroup L) v = c} //
        CuspOrbits.isotropicSubgroup hL hΓ a.1 = isotropicSubgroup N} ≃
    {d : DoubleCoset.Quotient
        ((⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L).toSubgroup : Set (OrthogonalGroup L))
          (MulAction.stabilizer (OrthogonalGroup L) N : Set (OrthogonalGroup L)) //
        CuspOrbits.isotropicSubgroup hL hΓ
          (LeanCategories.Lattices.Valued.cuspOrbitOfDoset
            (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
              FiniteIndexSubgroup L) N d).1 = isotropicSubgroup N} :=
  Equiv.subtypeEquiv (dosetQuotientOrbit
      (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
        FiniteIndexSubgroup L) N).symm fun a => by
    rw [show LeanCategories.Lattices.Valued.cuspOrbitOfDoset
        (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L) N
        ((dosetQuotientOrbit
          (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
            FiniteIndexSubgroup L) N).symm a) = a from
      (dosetQuotientOrbit
        (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L) N).apply_symm_apply a]

theorem dosetFibre_mk_iff (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) {k : ℕ}
    (N : PrimitiveIsotropic L k) (g : OrthogonalGroup L) :
    CuspOrbits.isotropicSubgroup hL hΓ
        (cuspOrbitOfDoset
          (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
            FiniteIndexSubgroup L) N
          (DoubleCoset.mk (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
            FiniteIndexSubgroup L).toSubgroup
            (MulAction.stabilizer (OrthogonalGroup L) N) g)).1 =
      isotropicSubgroup N ↔
      (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g ∈
        MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
          (isotropicSubgroup N) := by
  exact cuspOrbits_class_eq_iff_stabilizer hL hΓ N g

/-- A lift of a range element under the surjective restriction `ρ.rangeRestrict`. -/
noncomputable def rangeLift (hL : IsFractionFieldPerfect R L) :
    ↥(OrthogonalGroup.discriminantRepresentation hL).range → OrthogonalGroup L :=
  fun x => Classical.choose (MonoidHom.rangeRestrict_surjective _ x)

theorem rangeRestrict_rangeLift (hL : IsFractionFieldPerfect R L)
    (x : ↥(OrthogonalGroup.discriminantRepresentation hL).range) :
    (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict
      (rangeLift hL x) = x :=
  Classical.choose_spec (MonoidHom.rangeRestrict_surjective _ x)



variable {R : Type u} [CommRing R] [IsDomain R] {L : IntegralLatticeCat R}

/-- Two lifts whose values differ by an element of the stabilizer give the same double coset. -/
theorem doset_mk_eq_of_rangeRestrict_mul (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) {k : ℕ}
    (N : PrimitiveIsotropic L k) {x y s : OrthogonalGroup L}
    (hs : s ∈ MulAction.stabilizer (OrthogonalGroup L) N)
    (h : (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict y =
        (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict x *
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s) :
    DoubleCoset.mk (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L).toSubgroup
        (MulAction.stabilizer (OrthogonalGroup L) N) x =
      DoubleCoset.mk (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L).toSubgroup (MulAction.stabilizer (OrthogonalGroup L) N) y := by
  have h' : (OrthogonalGroup.discriminantRepresentation hL) y =
      (OrthogonalGroup.discriminantRepresentation hL) x *
        (OrthogonalGroup.discriminantRepresentation hL) s := by
    have := congrArg Subtype.val h
    simpa [MonoidHom.coe_rangeRestrict, Subgroup.coe_mul] using this
  have hk : x⁻¹ * y * s⁻¹ ∈ (OrthogonalGroup.discriminantRepresentation hL).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, h']
    group
  have hγ : x * (x⁻¹ * y * s⁻¹) * x⁻¹ ∈
      (⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ : FiniteIndexSubgroup L).toSubgroup :=
    (MonoidHom.normal_ker _).conj_mem _ hk x
  rw [DoubleCoset.eq]
  exact ⟨_, hγ, s, hs, by group⟩

/-- The fibre element represented by a stabilizer of the isotropic subgroup,
via a lift along `ρ.rangeRestrict`. -/
noncomputable def stabilizerLiftDoset (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) {k : ℕ}
    (N : PrimitiveIsotropic L k)
    (x : MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (isotropicSubgroup N)) : DosetFibre hL hΓ k N :=
  ⟨DoubleCoset.mk
      ((⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩ :
          FiniteIndexSubgroup L).toSubgroup)
      (MulAction.stabilizer (OrthogonalGroup L) N) (rangeLift hL x.1),
    (dosetFibre_mk_iff hL hΓ N (rangeLift hL x.1)).mpr
      (by rw [rangeRestrict_rangeLift hL x.1]; exact x.2)⟩

/-- The map from stabilizer cosets to the fibre on raw double cosets. Well-defined because two
lifts in the same coset differ by an element of the stabilizer of `N`. -/
noncomputable def cosetsToDosetFibre (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (isotropicSubgroup N) ⧸
      ((MulAction.stabilizer (OrthogonalGroup L) N).map
        (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict).subgroupOf
      (MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (isotropicSubgroup N)) →
        DosetFibre hL hΓ k N :=
  Quotient.lift (stabilizerLiftDoset hL hΓ N) (by
    intro a b hrel
    obtain ⟨s, hs, hes⟩ := Subgroup.mem_map.mp
      (Subgroup.mem_subgroupOf.mp ((QuotientGroup.leftRel_apply).mp hrel))
    have hcoe : ((a⁻¹ * b : MulAction.stabilizer ↥
          (OrthogonalGroup.discriminantRepresentation hL).range
          (isotropicSubgroup N)) :
        ↥(OrthogonalGroup.discriminantRepresentation hL).range) = a.1⁻¹ * b.1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hpair :
        (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict (rangeLift hL b.1) =
        (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict (rangeLift hL a.1) *
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s :=
      (rangeRestrict_rangeLift hL b.1).trans
        ((mul_inv_cancel_left a.1 b.1).symm.trans
          ((congrArg (fun t => a.1 * t) (hes.trans hcoe)).symm.trans
            (congrArg (fun t =>
              t * (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s)
              (rangeRestrict_rangeLift hL a.1)).symm))
    apply Subtype.ext
    exact doset_mk_eq_of_rangeRestrict_mul hL hΓ N hs hpair)

set_option maxHeartbeats 1200000 in
-- the two quotient inductions and the subgroup-coercion membership rewrites re-run
-- instance search through the discriminant bilinear object, which is expensive here
/-- Injective: equal fibre classes have equal stabilizer classes. -/
theorem cosetsToDosetFibre_injective (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    Function.Injective (cosetsToDosetFibre hL hΓ N) := by
  intro A B hxy
  induction A using Quotient.inductionOn with
  | _ a =>
  induction B using Quotient.inductionOn with
  | _ b =>
  have hxy' : stabilizerLiftDoset hL hΓ N a = stabilizerLiftDoset hL hΓ N b := hxy
  obtain ⟨γ, hγ, s, hs, hrel⟩ :=
    DoubleCoset.eq.mp (congrArg Subtype.val hxy')
  have hker : γ ∈ (OrthogonalGroup.discriminantRepresentation hL).ker := hγ
  have hγ1 : (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict γ = 1 := by
    rw [← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict]
    exact hker
  have hb : b.1 =
      a.1 * (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s := by
    calc b.1 = (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict
          (rangeLift hL b.1) := (rangeRestrict_rangeLift hL b.1).symm
      _ = (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict
            (γ * rangeLift hL a.1 * s) := congrArg _ hrel
      _ = (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict
            (γ * rangeLift hL a.1) *
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s := map_mul _ _ _
      _ = ((OrthogonalGroup.discriminantRepresentation hL).rangeRestrict γ *
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict
            (rangeLift hL a.1)) *
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s :=
            congrArg (fun t =>
              t * (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s)
              (map_mul _ _ _)
      _ = (1 * (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict
            (rangeLift hL a.1)) *
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s := by
            rw [hγ1]
      _ = (1 * a.1) *
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s := by
            rw [rangeRestrict_rangeLift hL a.1]
      _ = a.1 * (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s := by
            rw [one_mul]
  have hcoe : ((a⁻¹ * b : MulAction.stabilizer ↥
          (OrthogonalGroup.discriminantRepresentation hL).range
          (isotropicSubgroup N)) :
        ↥(OrthogonalGroup.discriminantRepresentation hL).range) = a.1⁻¹ * b.1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  exact ⟨s, hs, ((hcoe.trans
    ((congrArg (fun t => a.1⁻¹ * t) hb).trans (inv_mul_cancel_left a.1 _))).symm)⟩

set_option maxHeartbeats 1200000 in
-- unfolding the lifted fibre element to a raw double coset re-runs instance search
-- through the discriminant bilinear object, which is expensive here
/-- Surjective: every fibre class is the image of a stabilizer coset, represented by a lift
of the range restriction. -/
theorem cosetsToDosetFibre_surjective (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    Function.Surjective (cosetsToDosetFibre hL hΓ N) := by
  rintro ⟨⟨g⟩, hd⟩
  have hg : (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g ∈
      MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (isotropicSubgroup N) := (dosetFibre_mk_iff hL hΓ N g).mp hd
  refine ⟨QuotientGroup.mk
    ⟨(OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g, hg⟩, ?_⟩
  apply Subtype.ext
  have hone : (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g =
      (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict
        (rangeLift hL ((OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g)) *
      (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict (1 : OrthogonalGroup L) := by
    rw [rangeRestrict_rangeLift, map_one, mul_one]
  exact doset_mk_eq_of_rangeRestrict_mul hL hΓ N (Subgroup.one_mem _) hone

/-- The fibre theorem (#113 item 3): the fibre of the isotropic-class map at `N` is in bijection
with the stabilizer of `J_N` in the discriminant range, modulo the image of the stabilizer
of `N` under the range restriction. -/
noncomputable def cuspOrbitsStableEquivStabilizer (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex) {k : ℕ}
    (N : PrimitiveIsotropic L k) :
    StableFibre hL hΓ k N ≃
      MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
          (isotropicSubgroup N) ⧸
        ((MulAction.stabilizer (OrthogonalGroup L) N).map
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict).subgroupOf
        (MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
          (isotropicSubgroup N)) :=
  (stableFibreEquivDosetFibre hL hΓ).trans
    (Equiv.ofBijective (cosetsToDosetFibre hL hΓ N)
      ⟨cosetsToDosetFibre_injective hL hΓ N,
        cosetsToDosetFibre_surjective hL hΓ N⟩).symm

end LeanCategories.Lattices.Valued
