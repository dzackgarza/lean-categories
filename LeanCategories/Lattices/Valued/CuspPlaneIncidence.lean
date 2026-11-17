/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Cusps
public import LeanCategories.Lattices.Valued.CuspSchreierImage
public import LeanCategories.Lattices.Valued.CobleCusps

/-!
# The plane stabilizer's action on the primitive isotropic lines inside the plane

`CuspSchreierImage.planeStabilizerOrbitsEquivDoubleCoset` describes the `Stab_{O(L)}(P)`-orbits on
the `O(L)`-translates of a primitive isotropic line `V` by the double cosets of the plane stabilizer
and the line stabilizer. Its codomain is a subtype of the *ambient* orbit quotient and says nothing
about which of those lines lie in `P`, so it does not by itself describe a flag `V ⊂ P`.

This module supplies the incidence layer of the descent page's flag section
(`thm:descent-double-coset`, `sec-descent-flags` in
`.tmp-sources/research-discriminant-descent-b636d06011.md`, lines 84–104 and 125–131):

* **The plane stabilizer preserves containment** (`toSubmodule_le_of_mem_planeStabilizer_smul`) and
  reflects it at a line (`toSubmodule_le_iff_of_mem_planeStabilizer_smul`). Hence
  `Stab_{O(L)}(P)` acts on the actual subtype `PlaneLines L P` of primitive isotropic lines whose
  submodule lies in `P` (`PlaneLines.instSMul`, `PlaneLines.instMulAction`): the incidence condition
  is available for the action, not assumed of it.
* **The double-coset space of the existing equivalence has an invariant subset**
  (`planeIncidenceCosets P V`): the cosets whose representatives carry `V` into `P`. Membership is
  *defined* through one representative, and `mem_planeIncidenceCosets_iff_forall` proves every
  representative of a member carries `V` into `P` (`toSubmodule_le_iff_of_coset_eq`), so this is a
  property of the double coset and not of the chosen lift.
* **The incidence correspondence** (`planeIncidentOrbitsEquivDoubleCoset`): for the fixed ambient
  primitive-line orbit `O(L) · V`, the `Stab_{O(L)}(P)`-orbits that contain an incident line are
  exactly that invariant subset of double cosets. The orbit side (`PlaneIncidentOrbits P V`) is a
  subtype of the *existing* ambient orbit quotient rather than a second quotient of the incident
  lines, and the correspondence is the existing `planeStabilizerOrbitsEquivDoubleCoset` restricted
  along the incidence predicate (`planeIncidenceCosets_iff_isPlaneIncidentOrbit`) by
  `Equiv.subtypeEquiv`. Nothing of the double-coset/orbit dictionary is reproved, and the invariance
  of the incidence predicate is proved, not assumed.
* **The left/right convention is the existing one.** The quotient is
  `DoubleCoset.Quotient (Stab P : Set _) (Stab V : Set _)`: the left flanker is the plane stabilizer
  (the acting group) and the right one the line stabilizer, exactly as in
  `planeStabilizerOrbitsEquivDoubleCoset` and `DoubleCoset.orbitRelQuotientEquivDoubleCoset`, whose
  class of `g` corresponds to the `Stab(P)`-orbit of `g • V`.

## The worked flag of `T_Co`

`cobleLine_le_coblePlane` is proved from the displayed spans (`cobleLine` is `span {v}` and
`coblePlane` is `span {v, w}`, so the line is the span of one of the plane's two generators). It
gives the genuine incident line `cobleIncidentLine`, the incidence class `cobleIncidentOrbit`, and
`cobleIncidentOrbit_eq_identityCoset`: the Coble incidence class is the class of the double coset of
the identity, because the identity carries `v` into `span {v, w}`.

## What this module does not do

It does not prove the parent's finite-index plane-action computation, and it does not replace that
computation by a bound on an ambient discriminant kernel: no index, orbit count or finiteness claim
appears here. The descent page's `sec-descent-flags` reduces the flag count to the double cosets of
`Γ ∩ ρ⁻¹(F_{J,C})` and `ρ(Stab(P) ∩ Stab(L))` inside `ρ⁻¹(F_{J,C})`; that finite-index computation,
and the transitivity statement about the plane stabilizer on the primitive lines of one fixed
discriminant subgroup, remain owed by the parent.

## Search record (LC-09)

`scripts/formalization_corpus.py search` at the manifest head `9fdc1827` under `primitive isotropic
lines stabilizer orbits`, `flag incidence primitive isotropic sublattice stabilizer`, `PlaneLines
incident lines stabilizer action subtype`, `Plane incidence stabilizer double coset`, `MulAction
stabilizer subtype SMul preserve` and the Mathlib-style identifiers `Submodule.map_le_map_iff`,
`orbitRelQuotientEquivDoubleCoset`, `mem_stabilizer_iff smul submodule`. No source has this
incidence layer: the hits are TauCeti's `GroupTheory/DoubleCoset/{Inv,Orbits}.lean` (already ported
as `LeanCategories.ForMathlib.DoubleCosetOrbit`, which this module composes with) and TauCeti's own
`Submodule.map_le_map_iff_of_injective`, which Mathlib does not have; the containment transport here
uses Mathlib's `LinearMap.map_le_map_iff'`, which does. Everything below is glue between those and
the repository's existing owners `Cusps.PrimitiveIsotropic`, `CuspSchreierImage` and `CobleCusps`.
-/

@[expose] public section

open MulAction

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] {L : IntegralLatticeCat R}

/-! ## The plane stabilizer preserves and reflects containment in the plane -/

/-- An element of the plane stabilizer carries the plane's own submodule to itself. -/
theorem map_toSubmodule_eq_of_mem_planeStabilizer {P : PrimitiveIsotropic L 2}
    {g : OrthogonalGroup L} (hg : g ∈ MulAction.stabilizer (OrthogonalGroup L) P) :
    P.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P.toSubmodule :=
  congrArg PrimitiveIsotropic.toSubmodule (MulAction.mem_stabilizer_iff.mp hg)

/-- **The plane stabilizer preserves incidence**: the translate of a primitive isotropic line in
`P` by an element of `Stab_{O(L)}(P)` lies in `P`. -/
theorem toSubmodule_le_of_mem_planeStabilizer_smul {P : PrimitiveIsotropic L 2}
    {g : OrthogonalGroup L} (hg : g ∈ MulAction.stabilizer (OrthogonalGroup L) P)
    {q : PrimitiveIsotropic L 1} (hq : q.toSubmodule ≤ P.toSubmodule) :
    (g • q).toSubmodule ≤ P.toSubmodule := by
  change q.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) ≤ P.toSubmodule
  rw [← map_toSubmodule_eq_of_mem_planeStabilizer hg]
  exact Submodule.map_mono hq

/-- **The plane stabilizer reflects incidence.** An element of the plane stabilizer acts on the
carrier by an injective map and carries `P` to itself, so a translate of a line lies in `P` exactly
when the line does. This is what makes the incidence condition a property of the `Stab(P)`-orbit
of a line rather than of its representative. -/
theorem toSubmodule_le_iff_of_mem_planeStabilizer_smul {P : PrimitiveIsotropic L 2}
    {g : OrthogonalGroup L} (hg : g ∈ MulAction.stabilizer (OrthogonalGroup L) P)
    (q : PrimitiveIsotropic L 1) :
    (g • q).toSubmodule ≤ P.toSubmodule ↔ q.toSubmodule ≤ P.toSubmodule := by
  change q.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) ≤ P.toSubmodule ↔ _
  rw [show q.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) ≤ P.toSubmodule ↔
      q.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) ≤
        P.toSubmodule.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) from by
    rw [map_toSubmodule_eq_of_mem_planeStabilizer hg]]
  exact LinearMap.map_le_map_iff'
    (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective g.1))

/-! ## The plane stabilizer's action on the actual incident lines -/

/-- The primitive isotropic lines of `L` lying in the plane `P`: the actual incident lines, as the
subtype of the ambient line type on which the incidence predicate holds. -/
abbrev PlaneLines (L : IntegralLatticeCat R) (P : PrimitiveIsotropic L 2) : Type u :=
  {q : PrimitiveIsotropic L 1 // q.toSubmodule ≤ P.toSubmodule}

namespace PlaneLines

variable {P : PrimitiveIsotropic L 2}

/-- The plane stabilizer acts on the primitive isotropic lines lying in `P`, by the ambient action
of `O(L)` on primitive isotropic lines. `toSubmodule_le_of_mem_planeStabilizer_smul` witnesses that
the action lands in the subtype. -/
noncomputable instance instSMul :
    SMul (MulAction.stabilizer (OrthogonalGroup L) P) (PlaneLines L P) :=
  ⟨fun g q => ⟨g.1 • q.1, toSubmodule_le_of_mem_planeStabilizer_smul g.2 q.2⟩⟩

/-- The action of the plane stabilizer on the incident lines is an action: it inherits `one_smul`
and `mul_smul` from the action of `O(L)` on primitive isotropic lines. -/
noncomputable instance instMulAction :
    MulAction (MulAction.stabilizer (OrthogonalGroup L) P) (PlaneLines L P) where
  one_smul q := Subtype.ext (one_smul (OrthogonalGroup L) q.1)
  mul_smul g h q := Subtype.ext (mul_smul g.1 h.1 q.1)

/-- The incidence action is the ambient action on the underlying primitive isotropic line. -/
theorem coe_smul (g : MulAction.stabilizer (OrthogonalGroup L) P) (q : PlaneLines L P) :
    (g • q : PlaneLines L P).1 = g.1 • q.1 :=
  (rfl)

/-- **The orbit relation of the incidence action is the ambient one.** The inclusion of `PlaneLines`
into the primitive isotropic lines is equivariant, so two incident lines lie in one `Stab(P)`-orbit
for the incidence action exactly when they lie in one `Stab(P)`-orbit of the ambient action. This is
what lets `PlaneIncidentOrbits` be a subtype of the ambient orbit quotient of `Cusps` rather than a
second quotient of the incidence action. -/
theorem orbitRel_iff {P : PrimitiveIsotropic L 2} {q q' : PlaneLines L P} :
    orbitRel (MulAction.stabilizer (OrthogonalGroup L) P) (PlaneLines L P) q q' ↔
      orbitRel (MulAction.stabilizer (OrthogonalGroup L) P) (PrimitiveIsotropic L 1) q.1 q'.1 := by
  rw [orbitRel_apply, orbitRel_apply, MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk⟩

end PlaneLines

/-! ## The invariant subset of the double-coset space -/

/-- The double-coset space `Stab_{O(L)}(P) \ O(L) / Stab_{O(L)}(V)` in the convention of the
existing `planeStabilizerOrbitsEquivDoubleCoset`: the left flanker is the plane stabilizer (the
acting group) and the right one the line stabilizer. This is the type of the existing owner's
quotient, named so that the convention appears once. -/
noncomputable abbrev PlaneLineDoubleCoset (P : PrimitiveIsotropic L 2)
    (V : PrimitiveIsotropic L 1) : Type u :=
  DoubleCoset.Quotient (MulAction.stabilizer (OrthogonalGroup L) P : Set (OrthogonalGroup L))
    (MulAction.stabilizer (OrthogonalGroup L) V : Set (OrthogonalGroup L))

/-- The class of `g` in `Stab(P) \ O(L) / Stab(V)`, in the convention of
`planeStabilizerOrbitsEquivDoubleCoset`: the left flanker is the plane stabilizer (the acting group)
and the right one the line stabilizer. -/
noncomputable abbrev planeLineCoset (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1)
    (g : OrthogonalGroup L) : PlaneLineDoubleCoset P V :=
  DoubleCoset.mk (MulAction.stabilizer (OrthogonalGroup L) P)
    (MulAction.stabilizer (OrthogonalGroup L) V) g

/-- **The invariant subset of the double-coset space**: the double cosets whose representatives
carry `V` into `P`. The condition is imposed on one representative, and
`mem_planeIncidenceCosets_iff_forall` shows every representative of a member has it too. -/
noncomputable def planeIncidenceCosets (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) :
    Set (PlaneLineDoubleCoset P V) :=
  {d | ∃ g : OrthogonalGroup L, planeLineCoset P V g = d ∧ (g • V).toSubmodule ≤ P.toSubmodule}

/-- **Independence of the double-coset representative.** Two representatives of one double coset
differ by a left factor in the plane stabilizer and a right factor in the line stabilizer; the left
factor moves the line inside `P` exactly when it started there, and the right factor fixes `V`. -/
theorem toSubmodule_le_iff_of_mul_mem_stabilizer {P : PrimitiveIsotropic L 2}
    {V : PrimitiveIsotropic L 1} {g a b : OrthogonalGroup L}
    (ha : a ∈ MulAction.stabilizer (OrthogonalGroup L) P)
    (hb : b ∈ MulAction.stabilizer (OrthogonalGroup L) V) :
    ((a * g * b) • V).toSubmodule ≤ P.toSubmodule ↔ (g • V).toSubmodule ≤ P.toSubmodule := by
  have hbV : b • V = V := MulAction.mem_stabilizer_iff.mp hb
  have hsmul : (a * g * b) • V = a • (g • V) := by rw [mul_smul, mul_smul, hbV]
  rw [hsmul]
  exact toSubmodule_le_iff_of_mem_planeStabilizer_smul ha (g • V)

/-- The incidence condition depends only on the double coset, in the exact form the double-coset
relation gives: a representative `g'` of the class of `g` carries `V` into `P` exactly when `g`
does. -/
theorem toSubmodule_le_iff_of_coset_eq {P : PrimitiveIsotropic L 2}
    {V : PrimitiveIsotropic L 1} {g g' : OrthogonalGroup L}
    (h : planeLineCoset P V g' = planeLineCoset P V g) :
    (g' • V).toSubmodule ≤ P.toSubmodule ↔ (g • V).toSubmodule ≤ P.toSubmodule := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.eq.mp h
  exact (toSubmodule_le_iff_of_mul_mem_stabilizer (P := P) (V := V) ha hb).symm

/-- A double coset lies in the invariant subset exactly when its representative does. -/
theorem mem_planeIncidenceCosets_iff {P : PrimitiveIsotropic L 2} {V : PrimitiveIsotropic L 1}
    {g : OrthogonalGroup L} :
    planeLineCoset P V g ∈ planeIncidenceCosets P V ↔ (g • V).toSubmodule ≤ P.toSubmodule := by
  constructor
  · rintro ⟨g', hg', hle⟩
    exact (toSubmodule_le_iff_of_coset_eq hg').mp hle
  · intro h
    exact ⟨g, rfl, h⟩

/-- **The invariant subset is a property of the double coset.** Membership can be tested at every
representative, not only at the one used in the definition. -/
theorem mem_planeIncidenceCosets_iff_forall {P : PrimitiveIsotropic L 2}
    {V : PrimitiveIsotropic L 1} {d : PlaneLineDoubleCoset P V} :
    d ∈ planeIncidenceCosets P V ↔
      ∀ g : OrthogonalGroup L, planeLineCoset P V g = d → (g • V).toSubmodule ≤ P.toSubmodule := by
  constructor
  · rintro ⟨g₀, hg₀, hle⟩ g hg
    exact (toSubmodule_le_iff_of_coset_eq (hg.trans hg₀.symm)).mpr hle
  · intro h
    obtain ⟨g, hg⟩ := Quotient.mk_surjective d
    exact ⟨g, hg, h g hg⟩

/-! ## The incidence-restricted orbit set -/

/-- A `Stab(P)`-orbit of primitive isotropic lines is incidence-restricted when it contains an
actual incident line that is an `O(L)`-translate of `V`: the orbit is one the flag `V ⊂ P`
visits. -/
noncomputable def IsPlaneIncidentOrbit (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1)
    (o : orbitRel.Quotient (MulAction.stabilizer (OrthogonalGroup L) P)
      (PrimitiveIsotropic L 1)) : Prop :=
  ∃ q : PlaneLines L P, q.1 ∈ MulAction.orbit (OrthogonalGroup L) V ∧ Quotient.mk'' q.1 = o

/-- **The incidence-restricted orbit set** over the fixed ambient line orbit of `V`: the
`Stab(P)`-orbits on primitive isotropic lines that meet the incident lines of the `O(L)`-orbit of
`V`. It is a subtype of the ambient orbit quotient of `Cusps`, not a second quotient. -/
noncomputable def PlaneIncidentOrbits (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) :
    Type u :=
  {o : orbitRel.Quotient (MulAction.stabilizer (OrthogonalGroup L) P) (PrimitiveIsotropic L 1) //
    IsPlaneIncidentOrbit P V o}

/-- An incidence-restricted orbit meets the ambient `O(L)`-orbit of `V`, which is the codomain
condition of `planeStabilizerOrbitsEquivDoubleCoset`. -/
theorem exists_orbit_of_isPlaneIncidentOrbit {P : PrimitiveIsotropic L 2}
    {V : PrimitiveIsotropic L 1} {o : orbitRel.Quotient
      (MulAction.stabilizer (OrthogonalGroup L) P) (PrimitiveIsotropic L 1)}
    (ho : IsPlaneIncidentOrbit P V o) :
    ∃ q : PrimitiveIsotropic L 1, q ∈ MulAction.orbit (OrthogonalGroup L) V ∧
      Quotient.mk'' q = o := by
  obtain ⟨q, hq, hqo⟩ := ho
  exact ⟨q.1, hq, hqo⟩

/-- The incidence predicate is a property of the `Stab(P)`-orbit: testing it at any incident line of
the orbit gives the same answer, because the orbit stays inside the `O(L)`-orbit of `V`. -/
theorem isPlaneIncidentOrbit_mk_iff {P : PrimitiveIsotropic L 2} {V : PrimitiveIsotropic L 1}
    (q : PlaneLines L P) :
    IsPlaneIncidentOrbit P V (Quotient.mk'' q.1) ↔
      q.1 ∈ MulAction.orbit (OrthogonalGroup L) V := by
  constructor
  · rintro ⟨q', hq', hqo⟩
    obtain ⟨k, hk⟩ : ∃ k : MulAction.stabilizer (OrthogonalGroup L) P, k • q.1 = q'.1 := by
      rw [← MulAction.mem_orbit_iff]
      exact Quotient.exact hqo
    obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.mp hq'
    rw [MulAction.mem_orbit_iff]
    refine ⟨(k⁻¹).1 * m, ?_⟩
    rw [mul_smul, hm, ← hk]
    exact inv_smul_smul k q.1
  · intro hq
    exact ⟨q, hq, rfl⟩

/-! ## The incidence correspondence -/

/-- The existing double-coset/orbit dictionary computes the class of `g` as the orbit of `g • V`. -/
theorem planeStabilizerOrbitsEquivDoubleCoset_mk [IsDomain R] (P : PrimitiveIsotropic L 2)
    (V : PrimitiveIsotropic L 1) (g : OrthogonalGroup L) :
    planeStabilizerOrbitsEquivDoubleCoset P V (planeLineCoset P V g) =
      ⟨Quotient.mk'' (g • V), g • V, MulAction.mem_orbit V g, rfl⟩ :=
  Subtype.ext rfl

/-- **The incidence predicate on the double-coset side is the invariant subset.** The existing
equivalence carries a representative `g` to the orbit of `g • V`, so the double cosets whose
representatives carry `V` into `P` correspond exactly to the orbits containing an incident line. -/
theorem planeIncidenceCosets_iff_isPlaneIncidentOrbit [IsDomain R] (P : PrimitiveIsotropic L 2)
    (V : PrimitiveIsotropic L 1) (d : PlaneLineDoubleCoset P V) :
    d ∈ planeIncidenceCosets P V ↔
      IsPlaneIncidentOrbit P V ((planeStabilizerOrbitsEquivDoubleCoset P V d).1) := by
  constructor
  · rintro ⟨g, hg, hle⟩
    rw [← hg, planeStabilizerOrbitsEquivDoubleCoset_mk]
    exact ⟨⟨g • V, hle⟩, MulAction.mem_orbit V g, rfl⟩
  · rintro ⟨q, hq, hqo⟩
    obtain ⟨g₀, hg₀⟩ := Quotient.mk_surjective d
    have hsub : ((planeStabilizerOrbitsEquivDoubleCoset P V d).1) = Quotient.mk'' (g₀ • V) := by
      rw [← hg₀, planeStabilizerOrbitsEquivDoubleCoset_mk]
    have hmk : (Quotient.mk'' q.1 : orbitRel.Quotient
        (MulAction.stabilizer (OrthogonalGroup L) P) (PrimitiveIsotropic L 1)) =
        Quotient.mk'' (g₀ • V) := by
      rw [hqo, hsub]
    obtain ⟨k, hk⟩ : ∃ k : MulAction.stabilizer (OrthogonalGroup L) P,
        k • (g₀ • V) = q.1 := by
      rw [← MulAction.mem_orbit_iff]
      exact Quotient.exact hmk
    have hV : (k * g₀) • V = q.1 := by
      rw [mul_smul]
      exact hk
    have hcoset : planeLineCoset P V (k * g₀) = planeLineCoset P V g₀ := by
      rw [DoubleCoset.eq]
      exact ⟨(k⁻¹).1, (k⁻¹).2, 1, Subgroup.one_mem _, by simp⟩
    rw [← hg₀, mem_planeIncidenceCosets_iff]
    exact (toSubmodule_le_iff_of_coset_eq hcoset).mp (by rw [hV]; exact q.2)

/-- The existing double-coset/orbit dictionary restricted to the invariant subset: the cosets whose
representatives carry `V` into `P` map to the `Stab(P)`-orbits that contain an incident line. The
ambient orbit condition of the codomain is discharged by `exists_orbit_of_isPlaneIncidentOrbit`. -/
noncomputable def planeIncidentCosetsEquivAmbient [IsDomain R]
    (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) :
    {d : PlaneLineDoubleCoset P V //
      d ∈ planeIncidenceCosets P V} ≃ PlaneIncidentOrbits P V :=
  (Equiv.subtypeEquiv (planeStabilizerOrbitsEquivDoubleCoset P V)
      (planeIncidenceCosets_iff_isPlaneIncidentOrbit P V)).trans
    (Equiv.subtypeSubtypeEquivSubtype
      (p := fun o : orbitRel.Quotient (MulAction.stabilizer (OrthogonalGroup L) P)
        (PrimitiveIsotropic L 1) =>
        ∃ q : PrimitiveIsotropic L 1, q ∈ MulAction.orbit (OrthogonalGroup L) V ∧
          Quotient.mk'' q = o)
      (q := IsPlaneIncidentOrbit P V)
      (fun {_o} ho => exists_orbit_of_isPlaneIncidentOrbit ho))

/-- **The incidence correspondence.** For a primitive isotropic plane `P` and a primitive isotropic
line `V`, the `Stab_{O(L)}(P)`-orbits on the actual primitive isotropic lines of `L` that lie in `P`
and in the `O(L)`-orbit of `V` are the double cosets `Stab_{O(L)}(P) \ O(L) / Stab_{O(L)}(V)` whose
representatives carry `V` into `P`.

The orbit side is a subtype of the existing ambient orbit quotient, and the map is the inverse of
`planeIncidentCosetsEquivAmbient`, which is `Equiv.subtypeEquiv` applied to the existing
`planeStabilizerOrbitsEquivDoubleCoset`: the incidence predicate on orbits and the invariant subset
of double cosets are matched by `planeIncidenceCosets_iff_isPlaneIncidentOrbit`. Nothing of the
double-coset/orbit dictionary is reproved, and the invariance of the incidence predicate is
`mem_planeIncidenceCosets_iff_forall`. -/
noncomputable def planeIncidentOrbitsEquivDoubleCoset [IsDomain R]
    (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) :
    PlaneIncidentOrbits P V ≃ {d : PlaneLineDoubleCoset P V //
      d ∈ planeIncidenceCosets P V} :=
  (planeIncidentCosetsEquivAmbient P V).symm

/-- **The incidence correspondence is the existing double-coset/orbit equivalence, restricted.** The
existing equivalence, applied to the double coset of an incidence class, returns that class in the
ambient orbit quotient: the two descriptions agree, and the restricted correspondence invents no
second dictionary. -/
theorem planeStabilizerOrbitsEquivDoubleCoset_planeIncidentOrbits [IsDomain R]
    (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) (o : PlaneIncidentOrbits P V) :
    planeStabilizerOrbitsEquivDoubleCoset P V (planeIncidentOrbitsEquivDoubleCoset P V o).1 =
      ⟨o.1, exists_orbit_of_isPlaneIncidentOrbit o.2⟩ := by
  refine Subtype.ext ?_
  have hval : ((planeStabilizerOrbitsEquivDoubleCoset P V
      (planeIncidentOrbitsEquivDoubleCoset P V o).1)).1 =
      ((planeIncidentCosetsEquivAmbient P V) (planeIncidentOrbitsEquivDoubleCoset P V o)).1 :=
    rfl
  rw [hval]
  exact congrArg Subtype.val (Equiv.apply_symm_apply (planeIncidentCosetsEquivAmbient P V) o)

/-! ## The worked flag of `T_Co` -/

/-- **The Coble line lies in the Coble plane**, from their displayed spans: `cobleLine` is
`span {v}` and `coblePlane` is `span {v, w}`, so the line is the span of one generator of the
plane. -/
theorem cobleLine_le_coblePlane : cobleLine.toSubmodule ≤ coblePlane.toSubmodule := by
  have hline : cobleLine.toSubmodule = Submodule.span ℤ {coblePlaneV} :=
    @PrimitiveIsotropicVector.toLine_toSubmodule ℤ _ _ cobleLattice cobleLatticeCarrierTorsionFree
      cobleVector
  rw [hline]
  exact Submodule.span_mono (by simp)

/-- The genuine incident primitive isotropic line of `T_Co`: the Coble line, lying in the Coble
plane. -/
noncomputable def cobleIncidentLine : PlaneLines cobleLattice coblePlane :=
  ⟨cobleLine, cobleLine_le_coblePlane⟩

/-- **The Coble incidence class**: the orbit of the plane stabilizer `Stab_{O(T_Co)}(coblePlane)` on
the actual incident line `cobleLine`, inside the `O(T_Co)`-orbit of that line. -/
noncomputable def cobleIncidentOrbit : PlaneIncidentOrbits coblePlane cobleLine :=
  ⟨Quotient.mk'' cobleIncidentLine.1,
    ⟨cobleIncidentLine, MulAction.mem_orbit_self _, rfl⟩⟩

/-- The incidence action moves the Coble line inside the Coble plane: a concrete use of
`PlaneLines.instMulAction` at the worked flag. -/
theorem cobleIncidentLine_smul
    (g : MulAction.stabilizer (OrthogonalGroup cobleLattice) coblePlane) :
    ((g • cobleIncidentLine : PlaneLines cobleLattice coblePlane) :
      PrimitiveIsotropic cobleLattice 1) = g.1 • cobleLine :=
  PlaneLines.coe_smul g cobleIncidentLine

/-- **The Coble incidence class is the double coset of the identity.** The identity carries the
Coble line into the Coble plane, so `Stab(P)·1·Stab(V)` lies in the invariant subset and its class
is the incidence class of the Coble line under the correspondence. -/
theorem cobleIncidentOrbit_eq_identityCoset :
    planeIncidentOrbitsEquivDoubleCoset coblePlane cobleLine cobleIncidentOrbit =
      ⟨planeLineCoset coblePlane cobleLine 1,
        mem_planeIncidenceCosets_iff.mpr (by simpa using cobleLine_le_coblePlane)⟩ := by
  refine Subtype.ext ?_
  have h : planeStabilizerOrbitsEquivDoubleCoset coblePlane cobleLine
        (planeIncidentOrbitsEquivDoubleCoset coblePlane cobleLine cobleIncidentOrbit).1 =
      planeStabilizerOrbitsEquivDoubleCoset coblePlane cobleLine
        (planeLineCoset coblePlane cobleLine 1) := by
    rw [planeStabilizerOrbitsEquivDoubleCoset_planeIncidentOrbits,
      planeStabilizerOrbitsEquivDoubleCoset_mk]
    refine Subtype.ext ?_
    change Quotient.mk'' cobleLine =
      Quotient.mk'' ((1 : OrthogonalGroup cobleLattice) • cobleLine)
    rw [one_smul]
  exact (planeStabilizerOrbitsEquivDoubleCoset coblePlane cobleLine).injective h

/-- The incidence correspondence at the worked flag of `T_Co`. -/
noncomputable def coblePlaneIncidentOrbitsEquivDoubleCoset :
    PlaneIncidentOrbits coblePlane cobleLine ≃
      {d : PlaneLineDoubleCoset coblePlane cobleLine //
        d ∈ planeIncidenceCosets coblePlane cobleLine} :=
  planeIncidentOrbitsEquivDoubleCoset coblePlane cobleLine

end LeanCategories.Lattices.Valued
