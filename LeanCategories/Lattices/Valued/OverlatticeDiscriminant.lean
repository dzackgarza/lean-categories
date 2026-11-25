/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OverlatticeLattice

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-!
# The discriminant of an overlattice, inside the discriminant of the lattice below it

Nikulin, *Integral symmetric bilinear forms and some of their applications*, Math. USSR Izv. 14
(1980), §1.5, Prop. 1.5.1, p. 111: for the overlattice `M` of `L` attached to a totally isotropic
subgroup `Γ ⊆ A_L` (`Gluing.overlatticeFromIsotropicSubgroup`), the discriminant group of `M` is
`Γ^⊥/Γ` — the quotient of the orthogonal complement of `Γ` inside `A_L` by `Γ` itself. This is
#26's third result, and it needs `A_M = M^∨/M` to exist, which is what `Overlattice.lattice`
(`OverlatticeLattice.lean`) supplies.

## What is proved here

The class map of an overlattice: a vector `x` of the metric dual `M^∨ = dualSubmodule M.carrier`
pairs integrally with all of `M`, hence in particular with `L`, so its discriminant class `[x]`
lives in `A_L`. `Overlattice.discMap` is that map and `discMap_mem_glueOrthogonal` puts its image
in `Γ^⊥`, the orthogonal complement of the gluing subgroup `Γ = M/L`.

Modulo `Γ` it becomes `Overlattice.glueClassMap : ↥M.dualSubmodule →ₗ A_L ⧸ Γ`, and its two
halves are proved:

* `ker_glueClassMap`: **the kernel is the overlattice**, `ker = comap subtype M.carrier`. A class of
  `M^∨` vanishing in `A_L ⧸ Γ` comes from a vector of `M`, because its difference from that vector
  lies in `ker (metricDualToDiscriminant) = range toMetricDual`.
* `range_glueClassMap`: **the image is `Γ^⊥ ⧸ Γ`**, i.e.
  `Submodule.map (mkQ Γ) Γ^⊥`. Every class of `Γ^⊥` has a representative pairing integrally with all
  of `M`, so it comes from `M^∨`.

Those two are the isomorphism `A_M ≅ Γ^⊥/Γ` in quotient-free form: injectivity modulo `M` and
image exactly `Γ^⊥/Γ`. The single `≃ₗ` between `M^∨/M` and the range is *not* stated, and the
obstacle is not mathematics: `HasQuotient ↥M.dualSubmodule (Submodule R ↥M.dualSubmodule)` has no
instance, because `Submodule.hasQuotient` is stated for `Ring.toSemiring` while the ambient here
carries `CommRing.toCommSemiring.toSemiring` — the instance-path mismatch this repository already
knows from `ModuleCat.zsmul_eq_smul` (`Modules/Bilinear/Valued/Fixed.lean`). Manufacturing the
quotient through a `letI` does not help, since the type has to mention it. `COMPLAINTS.md` records
it. Note also that `↥M.carrier ⧸ _` fails the same way, so this is not about the metric dual.

The `whnf` divergence that blocked the previous attempt at this file is *not* the quotient codomain
after all: `glueClassMap` elaborates. It is the term `map_sub (metricDualToDiscriminant R L) a b`
used to *build* a rewrite with `.trans`; the form `Gluing.lean` uses —
`rw [show f (a - b) = f a - f b from map_sub f a b]` — elaborates immediately in the same place.
That is the whole difference between `whnf` timeouts at 1000000 heartbeats and a two-second file.

## Provenance

No Mathlib or TauCeti statement is ported: `discMap` and `glueClassMap` are this repository's own
`metricDualToValueDual`/`defectProjection` API, and TauCeti states the analogous facts only through
its `intermediateCarrierOfDiscriminantSubgroup` machinery, which has no counterpart here.

**For anyone porting later:** the missing object that made `A_M` unstatable was *projectivity* of
the overlattice's carrier, and TauCeti has no counterpart to port for it — `TauCeti.IntegralLattice`
is a submodule of a fixed `ℚ`-vector space with no projectivity field, so an overlattice there is a
lattice for free. `Overlattice.latticeOfPID` (`OverlatticeLattice.lean`) is this repository's own
answer (finiteness against the metric dual + torsion-freeness + `Module.free_of_finite_type_torsion_free'`).
Do not port a second lattice representation from TauCeti; there is nothing there to port.
-/

namespace Overlattice

variable {L : IntegralLatticeCat R}
variable {M : Overlattice R L}

omit [IsDomain R] in
/-- `fractionValueProjection` vanishes exactly on the image of `R`: the defining property of
`Frac(R)/R` used to read integrality back into `R`. -/
theorem mem_one_of_fractionValueProjection_eq_zero {w : FractionRing R}
    (h : fractionValueProjection R w = 0) : w ∈ (1 : Submodule R (FractionRing R)) := by
  rw [fractionValueProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  rwa [Submodule.one_eq_range]

/-- **The discriminant class map of an overlattice**: a vector of `M^∨` defines a functional on
the ambient lattice by integral pairing, hence a class in `A_L`. -/
noncomputable def discMap : ↥M.dualSubmodule →ₗ[R] L.obj.defect :=
  (BilinModuleCat.defectProjection L.obj).comp
    ((metricDualToValueDual R L).comp (Submodule.inclusion M.dualSubmodule_le_metricDual))

/-- The class of a dual vector is the discriminant class of its metric-dual representative. -/
theorem discMap_apply (x : ↥M.dualSubmodule) :
    discMap x = metricDualToDiscriminant R L
      ⟨x.1, M.dualSubmodule_le_metricDual x.2⟩ := rfl

/-- The orthogonal complement, inside the discriminant form of `L`, of the gluing subgroup `M/L`. -/
noncomputable def glueOrthogonal (hL : IsFractionFieldPerfect R L) : Submodule R L.obj.defect :=
  (discriminantBilinObject R L hL).orthogonalSubmodule M.glueSubgroup

/-- **The class map lands in `Γ^⊥`**: a dual vector of `M` pairs integrally with every element of
`M`, so its class is orthogonal to the gluing subgroup `Γ = M/L`. This is the first half of
`A_M ≅ Γ^⊥/Γ`. -/
theorem discMap_mem_glueOrthogonal (hL : IsFractionFieldPerfect R L)
    (x : ↥M.dualSubmodule) : discMap x ∈ glueOrthogonal (M := M) hL := by
  rw [glueOrthogonal]
  show ∀ p ∈ M.glueSubgroup,
    (discriminantBilinObject R L hL).pairing p (discMap x) = 0
  rintro p ⟨m, rfl⟩
  rw [LinearMap.comp_apply, discMap_apply, discriminant_pairing_metricDualToDiscriminant]
  have hmem : rationalizedForm R L (m : RationalSpan R L) (x : RationalSpan R L) ∈
      (1 : Submodule R (FractionRing R)) := by
    rw [rationalizedForm_isSymmetric R L]
    exact x.2 m.1 m.2
  rw [Submodule.mem_one] at hmem
  obtain ⟨r, hr⟩ := hmem
  change fractionValueProjection R
    (rationalizedForm R L (m : RationalSpan R L) (x : RationalSpan R L)) = 0
  rw [← hr, fractionValueProjection_algebraMap]

/-- The class map into `A_L ⧸ Γ`, `Γ = M/L`: a dual vector of `M` gives a class of `A_L`, modulo
the gluing subgroup. Its kernel and range are the two halves of `A_M ≅ Γ^⊥/Γ`. -/
noncomputable def glueClassMap : ↥M.dualSubmodule →ₗ[R] (L.obj.defect ⧸ M.glueSubgroup) where
  toFun x := Submodule.mkQ M.glueSubgroup (discMap x)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- **The kernel of the class map is the overlattice**: the classes of `M^∨` that vanish in
`A_L ⧸ Γ` are exactly those of `M`. This is the injectivity half of `A_M ≅ Γ^⊥/Γ`, stated without
forming the quotient `M^∨/M`. -/
theorem ker_glueClassMap (hL : IsFractionFieldPerfect R L) (M : Overlattice R L) :
    LinearMap.ker (glueClassMap (M := M)) =
      Submodule.comap (Submodule.subtype M.dualSubmodule) M.carrier := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  constructor
  · intro hx
    have hx' : discMap x ∈ M.glueSubgroup := by
      have h := hx
      change Submodule.mkQ M.glueSubgroup (discMap x) = 0 at h
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨m, hm⟩ := hx'
    rw [LinearMap.comp_apply] at hm
    have hdisc : discMap x = metricDualToDiscriminant R L
        ⟨x.1, M.dualSubmodule_le_metricDual x.2⟩ := rfl
    rw [hdisc] at hm
    have hdiff : (⟨x.1, M.dualSubmodule_le_metricDual x.2⟩ : ↥(metricDual R L)) -
        M.toMetricDual m ∈ LinearMap.ker (metricDualToDiscriminant R L) := by
      rw [LinearMap.mem_ker]
      rw [show metricDualToDiscriminant R L
            ((⟨x.1, M.dualSubmodule_le_metricDual x.2⟩ : ↥(metricDual R L)) - M.toMetricDual m) =
          metricDualToDiscriminant R L ⟨x.1, M.dualSubmodule_le_metricDual x.2⟩ -
            metricDualToDiscriminant R L (M.toMetricDual m) from
        map_sub (metricDualToDiscriminant R L) _ _]
      rw [hm, sub_self]
    rw [ker_metricDualToDiscriminant R L hL] at hdiff
    obtain ⟨l, hl⟩ := LinearMap.mem_range.mp hdiff
    have hsum : (⟨x.1, M.dualSubmodule_le_metricDual x.2⟩ : ↥(metricDual R L)) =
        M.toMetricDual m + LeanCategories.Lattices.Valued.toMetricDual R L l := by
      rw [hl]
      module
    have hsplit : (x.1 : RationalSpan R L) = (m : RationalSpan R L) + toRationalSpan R L l := by
      have h := congrArg (fun z : ↥(metricDual R L) => (z : RationalSpan R L)) hsum
      simp only [Submodule.coe_add] at h
      rw [show ((M.toMetricDual m : ↥(metricDual R L)) : RationalSpan R L) =
          (m : RationalSpan R L) from rfl,
        show ((LeanCategories.Lattices.Valued.toMetricDual R L l : ↥(metricDual R L)) :
          RationalSpan R L) = toRationalSpan R L l from rfl] at h
      exact h
    change (x.1 : RationalSpan R L) ∈ M.carrier
    rw [hsplit]
    exact M.carrier.add_mem m.2 (M.2.1 (LinearMap.mem_range_self (toRationalSpan R L) l))
  · intro hx
    have hx' : (x.1 : RationalSpan R L) ∈ M.carrier := hx
    have hcls : discMap x = metricDualToDiscriminant R L (M.toMetricDual ⟨x.1, hx'⟩) := by
      rw [show M.toMetricDual ⟨x.1, hx'⟩ =
          (⟨x.1, M.dualSubmodule_le_metricDual x.2⟩ : ↥(metricDual R L)) from rfl]
      exact discMap_apply x
    change Submodule.mkQ M.glueSubgroup (discMap x) = 0
    rw [hcls, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _

/-- **The range of the class map is `Γ^⊥ ⧸ Γ`**: the image of `M^∨` in `A_L ⧸ Γ` is the image of
the orthogonal complement of the gluing subgroup, i.e. exactly `Γ^⊥` modulo `Γ`. This is the
surjectivity half of `A_M ≅ Γ^⊥/Γ`. -/
theorem range_glueClassMap (hL : IsFractionFieldPerfect R L) (M : Overlattice R L) :
    LinearMap.range (glueClassMap (M := M)) =
      Submodule.map (Submodule.mkQ M.glueSubgroup) (glueOrthogonal (M := M) hL) := by
  ext z
  rw [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨discMap x, discMap_mem_glueOrthogonal hL x, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy⟩ := L.obj.defectProjection_surjective w
    have hclass : metricDualToDiscriminant R L (rieszToMetricDual R L hL y) = w := by
      rw [metricDualToDiscriminant, LinearMap.comp_apply,
        metricDualToValueDual_rieszToMetricDual, hy]
    have hx0 : ((rieszToMetricDual R L hL y : ↥(metricDual R L)) : RationalSpan R L) ∈
        M.dualSubmodule := by
      intro m hm
      have hp : metricDualToDiscriminant R L (M.toMetricDual ⟨m, hm⟩) ∈ M.glueSubgroup :=
        LinearMap.mem_range_self _ _
      have hzero := hw _ hp
      rw [← hclass] at hzero
      rw [discriminant_pairing_metricDualToDiscriminant R hL] at hzero
      rw [show ((M.toMetricDual ⟨m, hm⟩ : ↥(metricDual R L)) : RationalSpan R L) =
          (m : RationalSpan R L) from rfl,
        rationalizedForm_isSymmetric] at hzero
      exact mem_one_of_fractionValueProjection_eq_zero hzero
    refine ⟨⟨((rieszToMetricDual R L hL y : ↥(metricDual R L)) : RationalSpan R L), hx0⟩, ?_⟩
    have hcl : discMap (M := M) ⟨((rieszToMetricDual R L hL y : ↥(metricDual R L)) :
        RationalSpan R L), hx0⟩ = w := by
      rw [discMap_apply]
      exact hclass
    show Submodule.mkQ M.glueSubgroup (discMap _) = _
    rw [hcl]

end Overlattice

end LeanCategories.Lattices.Valued
