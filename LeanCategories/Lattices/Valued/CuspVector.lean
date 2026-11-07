/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CuspIsotropic

/-!
# Primitive isotropic vectors and their lines: the vector form of the cusp fibre theorem (#113)

Issue #113 states the descent fibre theorem for **primitive isotropic vectors** `v` and the
discriminant class `[v / d]` of `v` by its divisibility `d`, together with a worked instance for
`U ⊕ U`. What `CuspIsotropic.lean` proves is the same theorem for **primitive isotropic sublattices**
`N` (rank `1`: lines) and the subgroup `J_N = (N_ℚ ∩ L^∨)/N ⊆ A_L`, and what
`CuspWorkedInstance.lean` counts is **line** orbits. This module supplies the vector formulation and
the precise relation between the two, so that a generator is never identified with the cyclic
subgroup it spans without that equality being proved.

## What is proved here

* `PrimitiveIsotropicVector L`: a nonzero, indivisible, self-orthogonal vector, carrying the
  primitivity of the line it spans (`Module.IsTorsionFree` of the quotient, Nikulin's condition).
* `PrimitiveIsotropicVector.toLine`: the rank-1 primitive isotropic sublattice `R ∙ v`.
* `PrimitiveIsotropicVector.toLine_eq_iff`: two such vectors have the same line **iff** they are
  related by a unit, `∃ u : Rˣ, w = u • v`, proved from
  `Submodule.span_singleton_eq_span_singleton`. This is the equivalence the passage from vectors to
  lines needs.
* `PrimitiveIsotropicVector.lift`: the divisibility data of `v`, i.e. an element `w` of the metric
  dual with `d • w = v` that generates the saturation `L^∨ ∩ ℚ·v`; the issue's class `[v/d]` is
  `discriminantClass v D`, and `isotropicSubgroup_toLine_eq_span_class` proves
  `J_{R ∙ v} = R ∙ [v/d]`: the isotropic subgroup *is* the cyclic subgroup spanned by the
  discriminant class of `v/d`.

## Standing hypothesis

`NoZeroSMulDivisors R L.obj.carrier` — torsion-freeness of the carrier, which makes `R ∙ v` of rank
one and makes generators of a line differ by units. Every `IntegralLatticeCat` carrier is projective,
hence torsion-free over a domain; over `ℤ` the instance is found for the worked lattice.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The line spanned by a nonzero vector has rank one. Over a ring this is not
`finrank_span_singleton` (which needs a division ring); it is proved by the bijectivity of
`toSpanSingleton` onto the line, which is where torsion-freeness enters. -/
theorem finrank_span_singleton_eq_one {M : Type u} [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] {v : M} (hv : v ≠ 0) :
    Module.finrank R (Submodule.span R ({v} : Set M)) = 1 := by
  let P : Submodule R M := Submodule.span R ({v} : Set M)
  have hmem : v ∈ P := Submodule.mem_span_singleton_self v
  have htop : Submodule.span R ({⟨v, hmem⟩} : Set ↥P) = ⊤ := by
    refine Submodule.eq_top_iff'.mpr (fun y => ?_)
    have hy : (y : M) ∈ P := y.2
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c, hc⟩ := hy
    exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext (by simpa using hc)⟩
  have hinj : Function.Injective (LinearMap.toSpanSingleton R ↥P ⟨v, hmem⟩) := by
    intro a b hab
    have h : a • v = b • v := congrArg Subtype.val hab
    have h0 : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h0 with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hv
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton R ↥P ⟨v, hmem⟩) := by
    intro x
    have hx : x ∈ Submodule.span R ({⟨v, hmem⟩} : Set ↥P) := htop ▸ Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hx
    exact hx
  exact Module.finrank_of_bijective_toSpanSingleton (R := R) (M := ↥P) ⟨hinj, hsurj⟩

/-- A primitive isotropic vector of an integral lattice: nonzero, self-orthogonal, indivisible, and
spanning a primitive line. `indivisible` is primitivity of the vector (no nonunit multiple);
`primitiveSpan` is the same condition read on the quotient by the line, which is what
`PrimitiveIsotropic` consumes. -/
structure PrimitiveIsotropicVector (L : IntegralLatticeCat R) where
  /-- The underlying vector of the lattice. -/
  toVector : L.obj.carrier
  /-- It is nonzero, so it spans a line of rank one. -/
  nonzero : toVector ≠ 0
  /-- It is isotropic: its self-pairing vanishes. -/
  isotropic : L.obj.pairing toVector toVector = 0
  /-- It is indivisible: no nonunit multiple of another vector. -/
  indivisible : ∀ (c : R) (w : L.obj.carrier), toVector = c • w → IsUnit c
  /-- The line it spans is primitive: the quotient by it is torsion-free. -/
  primitiveSpan : IsPrimitiveSubmodule (Submodule.span R {toVector})

namespace PrimitiveIsotropicVector

variable {L : IntegralLatticeCat R}

/-- The line spanned by a primitive isotropic vector, as a primitive isotropic sublattice of rank
one. -/
noncomputable def toLine [NoZeroSMulDivisors R L.obj.carrier] (v : PrimitiveIsotropicVector L) :
    PrimitiveIsotropic L 1 where
  toSubmodule := Submodule.span R {v.toVector}
  isotropic := by
    intro x hx y hy
    rw [Submodule.mem_span_singleton] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    rw [← ha, ← hb, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      IntegralLatticeCat.asBilinForm_apply (L := L) v.toVector v.toVector, v.isotropic, mul_zero,
      mul_zero]
  finrank_eq := finrank_span_singleton_eq_one v.nonzero
  primitive := v.primitiveSpan

@[simp]
theorem toLine_toSubmodule [NoZeroSMulDivisors R L.obj.carrier] (v : PrimitiveIsotropicVector L) :
    v.toLine.toSubmodule = Submodule.span R {v.toVector} :=
  rfl

/-- The vector lies in its own line. -/
theorem toVector_mem_toLine [NoZeroSMulDivisors R L.obj.carrier] (v : PrimitiveIsotropicVector L) :
    v.toVector ∈ v.toLine.toSubmodule := by
  rw [toLine_toSubmodule]
  exact Submodule.mem_span_singleton_self v.toVector

/-- Two primitive isotropic vectors span the same line exactly when they differ by a unit. This is
the equivalence the vector formulation needs, and it is a consequence of
`Submodule.span_singleton_eq_span_singleton` at the torsion-free carrier. -/
theorem toLine_eq_iff [NoZeroSMulDivisors R L.obj.carrier]
    {v w : PrimitiveIsotropicVector L} :
    v.toLine = w.toLine ↔ ∃ u : Rˣ, w.toVector = u • v.toVector := by
  constructor
  · intro h
    have hspan : Submodule.span R {w.toVector} = Submodule.span R {v.toVector} := by
      rw [← toLine_toSubmodule, ← toLine_toSubmodule, h]
    rw [Submodule.span_singleton_eq_span_singleton] at hspan
    obtain ⟨z, hz⟩ := hspan
    exact ⟨z⁻¹, by rw [← hz]; exact (smul_inv_smul z⁻¹ w.toVector).symm⟩
  · rintro ⟨u, hu⟩
    apply PrimitiveIsotropic.ext
    rw [toLine_toSubmodule, toLine_toSubmodule, hu,
      Submodule.span_singleton_eq_span_singleton]
    exact ⟨u, rfl⟩

/-- A primitive isotropic vector is determined by its line and one representative. -/
theorem eq_smul_of_toLine_eq [NoZeroSMulDivisors R L.obj.carrier]
    {v w : PrimitiveIsotropicVector L} (h : v.toLine = w.toLine) :
    ∃ u : Rˣ, w.toVector = u • v.toVector :=
  toLine_eq_iff.mp h

end PrimitiveIsotropicVector

end LeanCategories.Lattices.Valued
namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

namespace PrimitiveIsotropicVector

variable {L : IntegralLatticeCat R}

omit [IsDomain R] in
/-- Two primitive isotropic vectors are equal as soon as their underlying vectors are: every other
field is a proposition. -/
@[ext]
theorem ext {v w : PrimitiveIsotropicVector L} (h : v.toVector = w.toVector) : v = w := by
  obtain ⟨a, an, ai, ad, ap⟩ := v
  obtain ⟨b, bn, bi, bd, bp⟩ := w
  simp only at h
  subst h
  rfl

omit [IsDomain R] in
/-- Primitivity of a submodule is invariant under a linear equivalence. -/
theorem isPrimitiveSubmodule_map_linearEquiv {M : Type u} [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] M) {P : Submodule R M} (h : IsPrimitiveSubmodule P) :
    IsPrimitiveSubmodule (P.map (e : M →ₗ[R] M)) := by
  have hq : Submodule.map (e : M →ₗ[R] M) P = P.map (e : M →ₗ[R] M) := rfl
  have he := Submodule.Quotient.equiv P (P.map (e : M →ₗ[R] M)) e hq
  rw [IsPrimitiveSubmodule, ← isTorsionFree_linearEquiv_iff he]
  exact h

variable [NoZeroSMulDivisors R L.obj.carrier]

omit [IsDomain R] [NoZeroSMulDivisors R L.obj.carrier] in
/-- The line spanned by a vector is transported to the image line by an isometry. -/
theorem span_smul_eq_map (g : OrthogonalGroup L) (v : PrimitiveIsotropicVector L) :
    Submodule.span R {g.1 v.toVector} =
      (Submodule.span R {v.toVector}).map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) := by
  rw [Submodule.map_span]
  simp

/-- `O(L)` acts on primitive isotropic vectors. -/
noncomputable instance : SMul (OrthogonalGroup L) (PrimitiveIsotropicVector L) where
  smul g v :=
    { toVector := g.1 v.toVector
      nonzero := fun h => v.nonzero ((LinearEquiv.map_eq_zero_iff g.1).mp h)
      isotropic := by rw [g.property]; exact v.isotropic
      indivisible := by
        intro c w hw
        refine v.indivisible c (g.1.symm w) ?_
        have h := congrArg (fun x => g.1.symm x) hw
        simpa using h
      primitiveSpan := by
        rw [span_smul_eq_map]
        exact isPrimitiveSubmodule_map_linearEquiv g.1 v.primitiveSpan }

omit [IsDomain R] [NoZeroSMulDivisors R L.obj.carrier] in
@[simp]
theorem smul_toVector (g : OrthogonalGroup L) (v : PrimitiveIsotropicVector L) :
    (g • v).toVector = g.1 v.toVector :=
  rfl

noncomputable instance : MulAction (OrthogonalGroup L) (PrimitiveIsotropicVector L) where
  one_smul v := by
    apply ext
    simp [smul_toVector]
  mul_smul g h v := by
    apply ext
    simp only [smul_toVector]
    rw [Subgroup.coe_mul]
    rfl

/-- The line of a translated vector is the translate of its line: `toLine` is `O(L)`-equivariant. -/
theorem toLine_smul (g : OrthogonalGroup L) (v : PrimitiveIsotropicVector L) :
    (g • v).toLine = g • v.toLine := by
  apply PrimitiveIsotropic.ext
  show Submodule.span R {g.1 v.toVector} = g • v.toLine.toSubmodule
  rw [OrthogonalGroup.smul_submodule_eq_map]
  exact span_smul_eq_map g v

section Lift

/-- The divisibility data of a primitive isotropic vector: the vector is `d` times an element `w` of
the metric dual, and `w` generates the saturation `L^∨ ∩ ℚ·v`. The divisor `d` is the divisibility
of `v` in the issue's sense and `w` is `v/d`; the class of `w` in `A_L` is the issue's `[v/d]`. -/
structure DivisibilityData (v : PrimitiveIsotropicVector L) where
  /-- The divisibility `d` of the vector. -/
  divisor : R
  /-- It is nonzero, so `v/d` makes sense. -/
  divisor_ne_zero : divisor ≠ 0
  /-- `v/d` in the metric dual. -/
  lift : metricDual R L
  /-- `v = d · (v/d)`. -/
  lift_spec : divisor • lift = toMetricDual R L v.toVector
  /-- `v/d` generates the saturation: it is the primitive element of `L^∨` in the direction of
  `v`. -/
  saturation_eq :
    saturation (Submodule.span R {toMetricDual R L v.toVector}) = Submodule.span R {lift}

omit [NoZeroSMulDivisors R L.obj.carrier] in
/-- The metric dual is torsion-free: it is a submodule of the rational span, where a nonzero integral
scalar can be cancelled after moving it into the fraction field. This is what makes `v/d` unique. -/
theorem metricDual_smul_inj (d : R) (hd : d ≠ 0) {x y : metricDual R L} (h : d • x = d • y) :
    x = y := by
  apply Subtype.ext
  have hd' : algebraMap R (FractionRing R) d ≠ 0 := by
    intro h0
    exact hd (IsFractionRing.injective R (FractionRing R) (by rw [h0, map_zero]))
  have hrat : (algebraMap R (FractionRing R) d) • (x : RationalSpan R L) =
      (algebraMap R (FractionRing R) d) • (y : RationalSpan R L) := by
    rw [IsScalarTower.algebraMap_smul (FractionRing R),
      IsScalarTower.algebraMap_smul (FractionRing R)]
    exact congrArg Subtype.val h
  calc (x : RationalSpan R L)
      = (algebraMap R (FractionRing R) d)⁻¹ •
          ((algebraMap R (FractionRing R) d) • (x : RationalSpan R L)) := by
        rw [smul_smul, inv_mul_cancel₀ hd', one_smul]
    _ = (algebraMap R (FractionRing R) d)⁻¹ •
          ((algebraMap R (FractionRing R) d) • (y : RationalSpan R L)) := by rw [hrat]
    _ = (y : RationalSpan R L) := by rw [smul_smul, inv_mul_cancel₀ hd', one_smul]

/-- The discriminant class `[v/d]` of a primitive isotropic vector. -/
noncomputable def discriminantClass {v : PrimitiveIsotropicVector L}
    (D : DivisibilityData v) : L.obj.defect :=
  metricDualToDiscriminant R L D.lift

/-- The image of the line of `v` in the metric dual is spanned by `toMetricDual v`. -/
theorem metricDualImage_toLine (v : PrimitiveIsotropicVector L) :
    metricDualImage (v.toLine (R := R)) =
      Submodule.span R {toMetricDual R L v.toVector} := by
  rw [metricDualImage, toLine_toSubmodule, Submodule.map_span]
  simp

/-- **The generator is the subgroup.** The isotropic subgroup `J_{R∙v} = (ℚ·v ∩ L^∨)/R∙v` is
exactly the cyclic subgroup of `A_L` spanned by the discriminant class `[v/d]` of `v/div(v)`. -/
theorem isotropicSubgroup_toLine_eq_span_class {v : PrimitiveIsotropicVector L}
    (D : DivisibilityData v) :
    isotropicSubgroup (v.toLine (R := R)) =
      Submodule.span R {discriminantClass D} := by
  simp only [isotropicSubgroup, metricDualSaturation]
  rw [metricDualImage_toLine, D.saturation_eq, Submodule.map_span]
  simp [discriminantClass]

omit [NoZeroSMulDivisors R L.obj.carrier] in
/-- An isometry fixing the vector fixes the primitive lift `v/d`, hence fixes the discriminant class
`[v/d]`. This is the well-definedness of `Γ·g·Stab(v) ↦ ρ(g)·[v/d]` on the right. -/
theorem fixes_discriminantClass (hL : IsFractionFieldPerfect R L)
    {v : PrimitiveIsotropicVector L} (D : DivisibilityData v) {h : OrthogonalGroup L}
    (hfix : h • v = v) :
    OrthogonalGroup.actOnDefect h (discriminantClass D) = discriminantClass D := by
  have hvec : h.1 v.toVector = v.toVector := congrArg PrimitiveIsotropicVector.toVector hfix
  have hlift : D.divisor • (OrthogonalGroup.actOnMetricDual h hL D.lift) = D.divisor • D.lift := by
    rw [← map_smul, D.lift_spec, actOnMetricDual_toMetricDual hL h v.toVector, hvec]
  have hfixlift : OrthogonalGroup.actOnMetricDual h hL D.lift = D.lift :=
    metricDual_smul_inj D.divisor D.divisor_ne_zero hlift
  rw [discriminantClass, ← OrthogonalGroup.metricDualToDiscriminant_actOnMetricDual h hL D.lift,
    hfixlift]

/-- The divisibility data transports along an isometry: the lift of `g • v` is `g · (v/d)`. -/
noncomputable def DivisibilityData.smul (hL : IsFractionFieldPerfect R L)
    (g : OrthogonalGroup L) {v : PrimitiveIsotropicVector L}
    (D : DivisibilityData v) : DivisibilityData (g • v) where
  divisor := D.divisor
  divisor_ne_zero := D.divisor_ne_zero
  lift := OrthogonalGroup.actOnMetricDual g hL D.lift
  lift_spec := by
    rw [smul_toVector, ← map_smul, D.lift_spec, actOnMetricDual_toMetricDual hL g v.toVector]
  saturation_eq := by
    have hspan : Submodule.span R {toMetricDual R L (g • v).toVector} =
        (Submodule.span R {toMetricDual R L v.toVector}).map
          (OrthogonalGroup.actOnMetricDual g hL : metricDual R L →ₗ[R] metricDual R L) := by
      rw [smul_toVector, ← actOnMetricDual_toMetricDual hL g v.toVector]
      rw [show ({OrthogonalGroup.actOnMetricDual g hL (toMetricDual R L v.toVector)} :
          Set (metricDual R L)) =
          (OrthogonalGroup.actOnMetricDual g hL : metricDual R L →ₗ[R] metricDual R L) ''
            {toMetricDual R L v.toVector} from by simp]
      rw [← Submodule.map_span]
    rw [hspan]
    have hsat := saturation_map_equiv (R := R) (M := metricDual R L) (M' := metricDual R L)
      (e := OrthogonalGroup.actOnMetricDual g hL)
      (P := Submodule.span R {toMetricDual R L v.toVector})
    rw [← hsat, D.saturation_eq, Submodule.map_span]
    simp

omit [NoZeroSMulDivisors R L.obj.carrier] in
/-- The discriminant class is equivariant: `[g v/d] = ρ(g)·[v/d]`. -/
theorem discriminantClass_smul (hL : IsFractionFieldPerfect R L) (g : OrthogonalGroup L)
    {v : PrimitiveIsotropicVector L} (D : DivisibilityData v) :
    discriminantClass (D.smul hL g) =
      OrthogonalGroup.actOnDefect g (discriminantClass D) := by
  exact OrthogonalGroup.metricDualToDiscriminant_actOnMetricDual g hL D.lift

end Lift

end PrimitiveIsotropicVector

end LeanCategories.Lattices.Valued
namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

section Orbits

variable {L : IntegralLatticeCat R} [NoZeroSMulDivisors R L.obj.carrier]

/-- `Γ ⊆ O(L)` acts on primitive isotropic vectors by restriction of scalars. -/
noncomputable instance primitiveIsotropicVectorGammaMulAction (Γ : FiniteIndexSubgroup L) :
    MulAction Γ.toSubgroup (PrimitiveIsotropicVector L) :=
  MulAction.compHom _ (Subgroup.subtype Γ.toSubgroup)

omit [IsDomain R] [NoZeroSMulDivisors R L.obj.carrier] in
/-- A double coset of `Γ` and the stabilizer of `v`, read off a vector in the `O(L)`-orbit of `v`.
The choice of the translating isometry is `Classical.choose` on the orbit membership. -/
noncomputable def dosetOfVectorOrbit (Γ : FiniteIndexSubgroup L) (v : PrimitiveIsotropicVector L)
    (u : {u : PrimitiveIsotropicVector L // u ∈ MulAction.orbit (OrthogonalGroup L) v}) :
    DoubleCoset.Quotient (Γ.toSubgroup : Set (OrthogonalGroup L))
      (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) :=
  DoubleCoset.mk _ _ (Classical.choose (MulAction.mem_orbit_iff.mp u.2))

/-- The `Γ`-orbit of `g • v` is a vector orbit inside the `O(L)`-orbit of `v`. -/
noncomputable def vectorOrbitOfDoset (Γ : FiniteIndexSubgroup L) (v : PrimitiveIsotropicVector L) :
    DoubleCoset.Quotient (Γ.toSubgroup : Set (OrthogonalGroup L))
        (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) →
      {o : Quotient (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropicVector L)) //
        ∃ u : PrimitiveIsotropicVector L, u ∈ MulAction.orbit (OrthogonalGroup L) v ∧
          Quotient.mk (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropicVector L)) u = o} :=
  Quotient.lift
    (fun g => ⟨Quotient.mk (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropicVector L)) (g • v),
      g • v, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩, rfl⟩)
    (by
      intro a b hab
      obtain ⟨γ, hγ, h, hh, rfl⟩ := (DoubleCoset.rel_iff
        (H := Γ.toSubgroup)
        (K := MulAction.stabilizer (OrthogonalGroup L) v)).mp hab
      simp only [Subtype.mk.injEq]
      have hstep : (γ * a * h) • v = (⟨γ, hγ⟩ : Γ.toSubgroup) • (a • v) := by
        rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp hh]
        rfl
      refine Quotient.sound (MulAction.orbitRel_apply.mpr
        ⟨⟨γ⁻¹, Γ.toSubgroup.inv_mem hγ⟩, ?_⟩)
      rw [hstep]
      show (γ⁻¹ : OrthogonalGroup L) • (γ • (a • v)) = a • v
      rw [smul_smul, inv_mul_cancel, one_smul])

omit [IsDomain R] [NoZeroSMulDivisors R L.obj.carrier] in
/-- Injective: equal `Γ`-orbits give equal double cosets. -/
theorem vectorOrbitOfDoset_injective (Γ : FiniteIndexSubgroup L)
    (v : PrimitiveIsotropicVector L) :
    Function.Injective (vectorOrbitOfDoset Γ v) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ g =>
  induction y using Quotient.inductionOn with
  | _ g' =>
  have h1 : Quotient.mk (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropicVector L)) (g • v) =
      Quotient.mk (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropicVector L)) (g' • v) := by
    have h := congrArg Subtype.val hxy
    exact h
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact h1))
  have hγ' : (γ : OrthogonalGroup L) • (g' • v) = g • v := hγ
  have hstab : (g⁻¹ * (γ : OrthogonalGroup L) * g') ∈
      MulAction.stabilizer (OrthogonalGroup L) v := by
    rw [MulAction.mem_stabilizer_iff]
    have hstep : (g⁻¹ * (γ : OrthogonalGroup L) * g') • v =
        g⁻¹ • ((γ : OrthogonalGroup L) • (g' • v)) := by
      simp [mul_smul]
    rw [hstep, hγ', inv_smul_smul]
  refine (DoubleCoset.eq (Γ.toSubgroup)
    (MulAction.stabilizer (OrthogonalGroup L) v) g g').mpr
    ⟨(γ : OrthogonalGroup L)⁻¹, Γ.toSubgroup.inv_mem γ.2,
      g⁻¹ * (γ : OrthogonalGroup L) * g', hstab, by group⟩

omit [IsDomain R] [NoZeroSMulDivisors R L.obj.carrier] in
/-- Surjective: every vector orbit inside the `O(L)`-orbit of `v` comes from a double coset. -/
theorem vectorOrbitOfDoset_surjective (Γ : FiniteIndexSubgroup L)
    (v : PrimitiveIsotropicVector L) :
    Function.Surjective (vectorOrbitOfDoset Γ v) := by
  intro p
  obtain ⟨c, hc⟩ := p
  obtain ⟨u, hu, huc⟩ := hc
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hu
  exact ⟨DoubleCoset.mk _ _ g, by
    apply Subtype.ext
    change Quotient.mk (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropicVector L)) (g • v) = c
    rw [hg, huc]⟩

/-- The `Γ`-orbits of the primitive isotropic vectors in the `O(L)`-orbit of `v` are the double
cosets of `Γ` and the stabilizer of the *vector* `v`. This is the vector analogue of
`dosetQuotientOrbit`, which uses the stabilizer of the line. -/
noncomputable def vectorOrbitsEquivDoubleCoset (Γ : FiniteIndexSubgroup L)
    (v : PrimitiveIsotropicVector L) :
    DoubleCoset.Quotient (Γ.toSubgroup : Set (OrthogonalGroup L))
        (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) ≃
      {o : Quotient (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropicVector L)) //
        ∃ u : PrimitiveIsotropicVector L, u ∈ MulAction.orbit (OrthogonalGroup L) v ∧
          Quotient.mk (MulAction.orbitRel Γ.toSubgroup (PrimitiveIsotropicVector L)) u = o} :=
  Equiv.ofBijective _ ⟨vectorOrbitOfDoset_injective Γ v, vectorOrbitOfDoset_surjective Γ v⟩

end Orbits

end LeanCategories.Lattices.Valued
namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R} [NoZeroSMulDivisors R L.obj.carrier]

section Fibre

variable (hL : IsFractionFieldPerfect R L)
variable (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex)

/-- The stable subgroup as a finite-index subgroup: the `Γ = ker ρ` of the issue. -/
noncomputable abbrev stableFiniteIndexSubgroup : FiniteIndexSubgroup L :=
  ⟨OrthogonalGroup.stableOrthogonalGroup hL, hΓ⟩

/-- The discriminant-class map of the issue: `Γ·g·Stab(v) ↦ ρ(g)·[v/d]`, for `Γ = ker ρ`. It is
well defined because `ker ρ` acts trivially on `A_L` (left factor) and the stabilizer of the vector
fixes the class `[v/d]` (right factor, by `discriminantClass_smul`). -/
noncomputable def stableVectorDiscriminantClassMap (v : PrimitiveIsotropicVector L)
    (D : PrimitiveIsotropicVector.DivisibilityData v) :
    DoubleCoset.Quotient (stableFiniteIndexSubgroup hL hΓ).toSubgroup
        (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) → L.obj.defect :=
  Quotient.lift (fun g => OrthogonalGroup.actOnDefect g
      (PrimitiveIsotropicVector.discriminantClass D)) (by
    intro a b hab
    obtain ⟨γ, hγ, h, hh, rfl⟩ := (DoubleCoset.rel_iff
      (H := (stableFiniteIndexSubgroup hL hΓ).toSubgroup)
      (K := MulAction.stabilizer (OrthogonalGroup L) v)).mp hab
    rw [OrthogonalGroup.actOnDefect_mul_apply, OrthogonalGroup.actOnDefect_mul_apply]
    have hγ1 : (OrthogonalGroup.actOnDefect (γ : OrthogonalGroup L) :
        L.obj.defect ≃ₗ[R] L.obj.defect) = 1 := by
      have hker : OrthogonalGroup.discriminantRepresentation hL (γ : OrthogonalGroup L) = 1 := hγ
      have h1 : (OrthogonalGroup.discriminantRepresentation hL (γ : OrthogonalGroup L)).1 =
          (1 : BilinModuleCat.OrthogonalGroup (discriminantBilinObject R L hL)).1 :=
        congrArg Subtype.val hker
      exact h1
    have hh1 : OrthogonalGroup.actOnDefect h
        (PrimitiveIsotropicVector.discriminantClass D) =
        PrimitiveIsotropicVector.discriminantClass D :=
      PrimitiveIsotropicVector.fixes_discriminantClass hL D (MulAction.mem_stabilizer_iff.mp hh)
    rw [hγ1, hh1]
    rfl)

omit [NoZeroSMulDivisors R L.obj.carrier] in
/-- Two lifts whose range restrictions differ by an element of the stabilizer of the *vector* give
the same double coset. This is the vector form of `doset_mk_eq_of_rangeRestrict_mul`; the argument is
the conjugate-in-kernel computation and does not see which object is being stabilized. -/
theorem doset_mk_eq_of_rangeRestrict_mul_vector (hL : IsFractionFieldPerfect R L)
    (hΓ : (OrthogonalGroup.stableOrthogonalGroup hL).FiniteIndex)
    (v : PrimitiveIsotropicVector L) {x y s : OrthogonalGroup L}
    (hs : s ∈ MulAction.stabilizer (OrthogonalGroup L) v)
    (h : (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict y =
        (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict x *
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict s) :
    DoubleCoset.mk (stableFiniteIndexSubgroup hL hΓ).toSubgroup
        (MulAction.stabilizer (OrthogonalGroup L) v) x =
      DoubleCoset.mk (stableFiniteIndexSubgroup hL hΓ).toSubgroup
        (MulAction.stabilizer (OrthogonalGroup L) v) y := by
  have h' : (OrthogonalGroup.discriminantRepresentation hL) y =
      (OrthogonalGroup.discriminantRepresentation hL) x *
        (OrthogonalGroup.discriminantRepresentation hL) s := by
    have := congrArg Subtype.val h
    simpa [MonoidHom.coe_rangeRestrict, Subgroup.coe_mul] using this
  have hk : x⁻¹ * y * s⁻¹ ∈ (OrthogonalGroup.discriminantRepresentation hL).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, h']
    group
  have hγ : x * (x⁻¹ * y * s⁻¹) * x⁻¹ ∈
      (stableFiniteIndexSubgroup hL hΓ).toSubgroup :=
    (MonoidHom.normal_ker _).conj_mem _ hk x
  rw [DoubleCoset.eq]
  exact ⟨_, hγ, s, hs, by group⟩

section FibreTheorem

/-- The fibre element of the discrimininal-class map represented by a stabilizer of the class, via a
lift along the surjective restriction `ρ.rangeRestrict`. -/
noncomputable def vectorStabilizerLiftDoset (v : PrimitiveIsotropicVector L)
    (D : PrimitiveIsotropicVector.DivisibilityData v)
    (x : MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (PrimitiveIsotropicVector.discriminantClass D)) :
    {q : DoubleCoset.Quotient (stableFiniteIndexSubgroup hL hΓ).toSubgroup
        (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) //
      stableVectorDiscriminantClassMap hL hΓ v D q =
        PrimitiveIsotropicVector.discriminantClass D} :=
  ⟨DoubleCoset.mk _ _ (rangeLift hL x.1), by
    show OrthogonalGroup.actOnDefect (rangeLift hL x.1)
      (metricDualToDiscriminant R L D.lift) = metricDualToDiscriminant R L D.lift
    show ((OrthogonalGroup.discriminantRepresentation hL).rangeRestrict (rangeLift hL x.1)) •
        (PrimitiveIsotropicVector.discriminantClass D) =
        PrimitiveIsotropicVector.discriminantClass D
    rw [rangeRestrict_rangeLift hL x.1]
    exact MulAction.mem_stabilizer_iff.mp x.2⟩

set_option maxHeartbeats 1200000 in
-- the nested quotients by `subgroupOf` of stabilizers run instance search through the discriminant
-- bilinear object, which is expensive here (as in `cosetsToDosetFibre`)
/-- The map from stabilizer cosets of the discriminant class to the fibre of the class map, on the
double-coset space of `Γ` and the stabilizer of the vector. -/
noncomputable def vectorStabilizerCosetsToFibre (v : PrimitiveIsotropicVector L)
    (D : PrimitiveIsotropicVector.DivisibilityData v) :
    MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (PrimitiveIsotropicVector.discriminantClass D) ⧸
      ((MulAction.stabilizer (OrthogonalGroup L) v).map
        (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict).subgroupOf
      (MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (PrimitiveIsotropicVector.discriminantClass D)) →
      {q : DoubleCoset.Quotient (stableFiniteIndexSubgroup hL hΓ).toSubgroup
          (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) //
        stableVectorDiscriminantClassMap hL hΓ v D q =
          PrimitiveIsotropicVector.discriminantClass D} :=
  Quotient.lift (vectorStabilizerLiftDoset hL hΓ v D) (by
    intro a b hrel
    obtain ⟨s, hs, hes⟩ := Subgroup.mem_map.mp
      (Subgroup.mem_subgroupOf.mp ((QuotientGroup.leftRel_apply).mp hrel))
    have hcoe : ((a⁻¹ * b : MulAction.stabilizer ↥
        (OrthogonalGroup.discriminantRepresentation hL).range
        (PrimitiveIsotropicVector.discriminantClass D)) :
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
    show (DoubleCoset.mk (stableFiniteIndexSubgroup hL hΓ).toSubgroup
        (MulAction.stabilizer (OrthogonalGroup L) v) (rangeLift hL a.1) : DoubleCoset.Quotient
          (stableFiniteIndexSubgroup hL hΓ).toSubgroup
          (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L))) =
      DoubleCoset.mk (stableFiniteIndexSubgroup hL hΓ).toSubgroup
        (MulAction.stabilizer (OrthogonalGroup L) v) (rangeLift hL b.1)
    exact doset_mk_eq_of_rangeRestrict_mul_vector hL hΓ v hs hpair)

set_option maxHeartbeats 1200000 in
-- unfolding the lifted fibre element to a raw double coset re-runs instance search through the
-- discriminant bilinear object, which is expensive here (as in `cosetsToDosetFibre_injective`)
/-- Injective: equal fibre elements have equal stabilizer cosets. -/
theorem vectorStabilizerCosetsToFibre_injective (v : PrimitiveIsotropicVector L)
    (D : PrimitiveIsotropicVector.DivisibilityData v) :
    Function.Injective (vectorStabilizerCosetsToFibre hL hΓ v D) := by
  intro A B hxy
  induction A using Quotient.inductionOn with
  | _ a =>
  induction B using Quotient.inductionOn with
  | _ b =>
  have hxy' : vectorStabilizerLiftDoset hL hΓ v D a = vectorStabilizerLiftDoset hL hΓ v D b := hxy
  obtain ⟨γ, hγ, s, hs, hrel⟩ :=
    (DoubleCoset.eq ((stableFiniteIndexSubgroup hL hΓ).toSubgroup)
        (MulAction.stabilizer (OrthogonalGroup L) v)
        (rangeLift hL a.1) (rangeLift hL b.1)).mp (congrArg Subtype.val hxy')
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
          (PrimitiveIsotropicVector.discriminantClass D)) :
        ↥(OrthogonalGroup.discriminantRepresentation hL).range) = a.1⁻¹ * b.1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  exact ⟨s, hs, ((hcoe.trans
    ((congrArg (fun t => a.1⁻¹ * t) hb).trans (inv_mul_cancel_left a.1 _))).symm)⟩

set_option maxHeartbeats 1200000 in
-- as above: the fibre element is unfolded to a raw double coset
/-- Surjective: every fibre element is the image of a stabilizer coset, represented by a lift of the
range restriction. -/
theorem vectorStabilizerCosetsToFibre_surjective (v : PrimitiveIsotropicVector L)
    (D : PrimitiveIsotropicVector.DivisibilityData v) :
    Function.Surjective (vectorStabilizerCosetsToFibre hL hΓ v D) := by
  rintro ⟨⟨g⟩, hd⟩
  have hg : (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g ∈
      MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
        (PrimitiveIsotropicVector.discriminantClass D) := hd
  refine ⟨QuotientGroup.mk
    ⟨(OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g, hg⟩, ?_⟩
  apply Subtype.ext
  have hone : (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g =
      (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict
        (rangeLift hL ((OrthogonalGroup.discriminantRepresentation hL).rangeRestrict g)) *
      (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict (1 : OrthogonalGroup L) := by
    rw [rangeRestrict_rangeLift, map_one, mul_one]
  exact doset_mk_eq_of_rangeRestrict_mul_vector hL hΓ v (Subgroup.one_mem _) hone

/-- **The fibre theorem in vector form** (#113): for `Γ = ker ρ`, a primitive isotropic vector `v`
with divisibility data `d`, `v/d`, the fibre of `Γ·g·Stab(v) ↦ ρ(g)·[v/d]` over the discriminant
class `[v/d]` is the stabilizer of `[v/d]` in `ρ(O(L))` modulo `ρ(Stab_{O(L)}(v))`.

Here `ρ` runs into `O(q_L)` and the stabilizer is taken in its range `ρ(O(L))`; that range *is*
`O(q_L)` exactly when `ρ` is surjective, which is the hypothesis the issue attaches to the
discriminant-descent statement. Nothing else about `ρ` is assumed: `ρ.rangeRestrict` is always
surjective onto the range, so the argument never needs surjectivity onto `O(q_L)`. -/
noncomputable def vectorFibreEquivStabilizer (v : PrimitiveIsotropicVector L)
    (D : PrimitiveIsotropicVector.DivisibilityData v) :
    {q : DoubleCoset.Quotient (stableFiniteIndexSubgroup hL hΓ).toSubgroup
        (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) //
      stableVectorDiscriminantClassMap hL hΓ v D q =
        PrimitiveIsotropicVector.discriminantClass D} ≃
      MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
          (PrimitiveIsotropicVector.discriminantClass D) ⧸
        ((MulAction.stabilizer (OrthogonalGroup L) v).map
          (OrthogonalGroup.discriminantRepresentation hL).rangeRestrict).subgroupOf
        (MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation hL).range
          (PrimitiveIsotropicVector.discriminantClass D)) :=
  (Equiv.ofBijective _ ⟨vectorStabilizerCosetsToFibre_injective hL hΓ v D,
    vectorStabilizerCosetsToFibre_surjective hL hΓ v D⟩).symm

end FibreTheorem

end Fibre

end LeanCategories.Lattices.Valued
