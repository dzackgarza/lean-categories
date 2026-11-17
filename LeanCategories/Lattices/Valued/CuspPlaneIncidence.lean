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
* **The image of the plane stabilizer in the plane's automorphism group** (`planeStabilizerImage P`,
  written `Δ` below): the range of `planeStabilizerRestrictHom`, the restriction of a plane
  stabilizer element to an equivalence of `↥P.toSubmodule`. Its action on `PlaneLines L P`
  (`instMulActionPlaneStabilizerImage`) is the transport of the line by the plane equivalence, and
  `planeLineTransport_restrict_coe` identifies it with the ambient stabilizer action read through
  the image. This is the group `sec-descent-flags` counts orbits for, and it is not `O(L)`'s
  stabilizer turned into automorphisms of `P` by a choice of `GL(2, ℤ)` coordinates: the
  coordinates are a later link.
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

**Nor does it state the count.** `Δ` and its action are here, but the number of `Δ`-orbits on
`PlaneLines L P` is not stated and must not be stated yet: it needs the two links that follow the
image. First a `ℤ`-basis of `P` and the transport of `Δ` into `GL(2, ℤ)` in that basis — the basis
is what turns `↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule` into a subgroup of `GL(2, ℤ)`, and `Δ` is only
a subgroup of `GL(2, ℤ)` *after* that choice. Second the correspondence between `PlaneLines L P` and
the `ℚ`-points of `P*` in the same basis, which is what makes the orbits of `Δ` on lines the cusps
of a subgroup of `GL(2, ℤ)`; `ForMathlib/ModularCuspsGL2.lean` then gives finiteness and the bound
`natCard_cuspOrbits_le_index_GL2`, still not an exact count. A count stated before the
correspondence would be a count of a different object — for instance of `GL(2, ℤ)` itself, which
the source says is not the `T_Co` image (there the image is a proper subgroup of the finite
stabilizer, `|F/S| = 8`). Note also that the "adapted basis" the source asks for has no content for
an isotropic plane: the form restricted to `P` vanishes identically, so every `ℤ`-basis of `P` is
adapted.

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


/-! ## The image of the plane stabilizer in the plane's automorphism group

`PlaneLines.instMulAction` above acts with the *whole* plane stabilizer
`↥(MulAction.stabilizer (OrthogonalGroup L) P)`. The descent page's `sec-descent-flags` counts
something else: the orbits of the *image* `Δ` of that stabilizer in the automorphism group of the
plane, because the stabilizer's action on the lines of `P` factors through its restriction to `P`,
and for `T_Co` the source records that integral image as a proper subgroup of the finite stabilizer
(the parabolic `S` of `F`, `|F/S| = 8`). This section supplies that image and its action.

**The target group.** `planeStabilizerRestrictHom P` lands in
`↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule`, not in a separate `Aut(P)`: the two coincide, because `P` is
isotropic, so the form restricted to `P` vanishes identically and every linear automorphism of the
carrier `↥P.toSubmodule` preserves it. The development uses the submodule equivalence group because
that is the group a later `ℤ`-basis of `P` reads off as `GL(2, ℤ)`; introducing a second name for
`Aut(P)` here would add an identification with no content behind it.

**Why the well-definedness is not free.** `δ ∈ Δ` is an automorphism of `P`, not of `L`
(`O(L)`-elements do not enter `Aut(P)` in a way that could be lifted back), so
`IsPrimitiveSubmodule.map_equiv_iff` cannot be applied to a line of `L` directly. The transport
`planeSubmoduleTransport` is applied to the line inside `P`, and primitivity is carried across by
`isPrimitiveSubmodule_comap_subtype_iff`, which proves that `L ⧸ q` is torsion-free exactly when
`P ⧸ q` is for `q ≤ P` with `P` primitive. That is where the primitivity of the image lives, and it
is why the action needs `[IsDomain R]` (the saturation form of primitivity) while the rest of the
section does not.

## Search record (LC-09)

`scripts/formalization_corpus.py batch` at the manifest head used by this worktree, under
`restriction isometry invariant submodule linear equivalence stabilizer`,
`Submodule.equivMapOfInjective map_eq_top`, `MulAction.stabilizer map restrict monoid hom
automorphism group`, `primitive submodule saturation image linear equivalence torsion free
quotient`, `intermediate submodule primitive quotient torsion free transitivity`,
`primitive vector image automorphism primitive sublattice`, `Submodule.equivMapOfInjective`,
`hyperbolic partner isotropic vector` and `Projectivization.mk` (the last two for the still-open
basis and line/`ℙ¹(ℚ)` links). No source has the image or the primitivity transport: the hits are
Mathlib's `Submodule.equivMapOfInjective` and `Submodule.inclusion`, TauCeti's totally isotropic
subspaces (field-level hyperbolic partners, which `Quotient.exists_hyperbolicPartner` already
mirrors), and the repository's own `Sublattice.isPrimitiveSubmodule_iff_saturation_eq`,
`IsPrimitiveSubmodule.map_equiv_iff` and `Sublattice.saturation`. Everything below is glue among
those and `map_toSubmodule_eq_of_mem_planeStabilizer`.
-/

/-- The restriction of an element of the plane stabilizer to the plane. -/
noncomputable def planeStabilizerRestrict {P : PrimitiveIsotropic L 2}
    (g : ↥(MulAction.stabilizer (OrthogonalGroup L) P)) :
    ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule :=
  (Submodule.equivMapOfInjective (p := P.toSubmodule)
      (g.1.1 : L.obj.carrier →ₗ[R] L.obj.carrier) (LinearEquiv.injective g.1.1)).trans
    (LinearEquiv.ofEq _ _ (map_toSubmodule_eq_of_mem_planeStabilizer g.2))

theorem planeStabilizerRestrict_apply_coe {P : PrimitiveIsotropic L 2}
    (g : ↥(MulAction.stabilizer (OrthogonalGroup L) P)) (x : ↥P.toSubmodule) :
    (planeStabilizerRestrict g x : L.obj.carrier) = g.1.1 x := by
  simp [planeStabilizerRestrict]

theorem planeStabilizerRestrict_one {P : PrimitiveIsotropic L 2} :
    planeStabilizerRestrict (1 : ↥(MulAction.stabilizer (OrthogonalGroup L) P)) = 1 := by
  refine LinearEquiv.ext fun x => ?_
  apply Subtype.ext
  rw [planeStabilizerRestrict_apply_coe]
  rfl

theorem planeStabilizerRestrict_mul {P : PrimitiveIsotropic L 2}
    (g h : ↥(MulAction.stabilizer (OrthogonalGroup L) P)) :
    planeStabilizerRestrict (g * h) =
      planeStabilizerRestrict g * planeStabilizerRestrict h := by
  refine LinearEquiv.ext fun x => ?_
  apply Subtype.ext
  change ((planeStabilizerRestrict (g * h)) x : L.obj.carrier) =
    ((planeStabilizerRestrict g) ((planeStabilizerRestrict h) x) : L.obj.carrier)
  rw [planeStabilizerRestrict_apply_coe, planeStabilizerRestrict_apply_coe,
    planeStabilizerRestrict_apply_coe]
  rfl

noncomputable def planeStabilizerRestrictHom (P : PrimitiveIsotropic L 2) :
    ↥(MulAction.stabilizer (OrthogonalGroup L) P) →*
      (↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule) where
  toFun := planeStabilizerRestrict
  map_one' := planeStabilizerRestrict_one
  map_mul' := planeStabilizerRestrict_mul

noncomputable def planeStabilizerImage (P : PrimitiveIsotropic L 2) :
    Subgroup (↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule) :=
  (planeStabilizerRestrictHom P).range

theorem mem_planeStabilizerImage {P : PrimitiveIsotropic L 2}
    {δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule} :
    δ ∈ planeStabilizerImage P ↔ ∃ g, planeStabilizerRestrict g = δ :=
  MonoidHom.mem_range

/-- The image of the submodule `q ≤ P` under an equivalence of the plane. -/
noncomputable def planeSubmoduleTransport {P : PrimitiveIsotropic L 2}
    (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
    (q : Submodule R L.obj.carrier) (hq : q ≤ P.toSubmodule) : Submodule R L.obj.carrier :=
  (P.toSubmodule.subtype.comp (δ.toLinearMap.comp (Submodule.inclusion hq))).range

theorem mem_planeSubmoduleTransport {P : PrimitiveIsotropic L 2}
    {δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule} {q : Submodule R L.obj.carrier}
    {hq : q ≤ P.toSubmodule} {x : L.obj.carrier} :
    x ∈ planeSubmoduleTransport δ q hq ↔
      ∃ y : ↥q, (δ (Submodule.inclusion hq y) : L.obj.carrier) = x := by
  simp [planeSubmoduleTransport, LinearMap.mem_range]

theorem planeSubmoduleTransport_le {P : PrimitiveIsotropic L 2}
    (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
    (q : Submodule R L.obj.carrier) (hq : q ≤ P.toSubmodule) :
    planeSubmoduleTransport δ q hq ≤ P.toSubmodule := by
  rintro x ⟨y, rfl⟩
  exact (δ (Submodule.inclusion hq y)).2

theorem planeSubmoduleTransportLinearMap_injective {P : PrimitiveIsotropic L 2}
    (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
    (q : Submodule R L.obj.carrier) (hq : q ≤ P.toSubmodule) :
    Function.Injective (P.toSubmodule.subtype.comp (δ.toLinearMap.comp
      (Submodule.inclusion hq))) := by
  intro a b hab
  have h2 : δ (Submodule.inclusion hq a) = δ (Submodule.inclusion hq b) :=
    Subtype.val_injective hab
  have h3 : Submodule.inclusion hq a = Submodule.inclusion hq b := δ.injective h2
  exact Subtype.ext (by simpa using congrArg Subtype.val h3)

noncomputable def planeSubmoduleTransportEquiv {P : PrimitiveIsotropic L 2}
    (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
    (q : Submodule R L.obj.carrier) (hq : q ≤ P.toSubmodule) :
    ↥q ≃ₗ[R] ↥(planeSubmoduleTransport δ q hq) :=
  LinearEquiv.ofInjective _ (planeSubmoduleTransportLinearMap_injective δ q hq)

theorem planeSubmoduleTransport_finrank {P : PrimitiveIsotropic L 2}
    (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
    (q : Submodule R L.obj.carrier) (hq : q ≤ P.toSubmodule) {k : ℕ}
    (hk : Module.finrank R ↥q = k) :
    Module.finrank R ↥(planeSubmoduleTransport δ q hq) = k := by
  rw [← (planeSubmoduleTransportEquiv δ q hq).finrank_eq, hk]

theorem planeSubmoduleTransport_isotropic {P : PrimitiveIsotropic L 2}
    (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
    (q : Submodule R L.obj.carrier) (hq : q ≤ P.toSubmodule) :
    IsIsotropicSubmodule L (planeSubmoduleTransport δ q hq) := by
  intro x hx y hy
  exact P.isotropic x (planeSubmoduleTransport_le δ q hq hx) y
    (planeSubmoduleTransport_le δ q hq hy)

/-- **Primitivity passes between `q` and `q` read inside a primitive `P`**: for `q ≤ P` with `P`
primitive, `L ⧸ q` is torsion-free exactly when `P ⧸ q` is. The forward direction lifts a torsion
element of `P ⧸ q` to `L ⧸ q`; the converse first pushes a torsion element of `L ⧸ q` into `P`
using primitivity of `P`, then uses primitivity of `q` inside `P`. -/
theorem isPrimitiveSubmodule_comap_subtype_iff {M : Type u} [AddCommGroup M] [Module R M]
    [IsDomain R] {P q : Submodule R M} (hq : q ≤ P) (hP : IsPrimitiveSubmodule P) :
    IsPrimitiveSubmodule (q.comap P.subtype) ↔ IsPrimitiveSubmodule q := by
  have hPsat : saturation P = P := (isPrimitiveSubmodule_iff_saturation_eq P).mp hP
  constructor
  · intro hQP
    rw [(isPrimitiveSubmodule_iff_saturation_eq (q.comap P.subtype))] at hQP
    rw [(isPrimitiveSubmodule_iff_saturation_eq q)]
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hax⟩ := mem_saturation_iff q x |>.mp hx
      have haxP : a • x ∈ P := hq hax
      have hxP : x ∈ P := by
        rw [← hPsat]
        exact mem_saturation_iff P x |>.mpr ⟨a, ha, haxP⟩
      obtain ⟨b, hb, hbax⟩ : ∃ b : R, b ≠ 0 ∧ b • (⟨x, hxP⟩ : ↥P) ∈ q.comap P.subtype := by
        refine ⟨a, ha, ?_⟩
        rw [Submodule.mem_comap]
        simpa using hax
      have hmem : (⟨x, hxP⟩ : ↥P) ∈ saturation (q.comap P.subtype) :=
        mem_saturation_iff (q.comap P.subtype) _ |>.mpr ⟨b, hb, hbax⟩
      rw [hQP] at hmem
      exact hmem
    · intro hx
      exact mem_saturation_iff q x |>.mpr ⟨1, one_ne_zero, by simpa using hx⟩
  · intro hQ
    rw [(isPrimitiveSubmodule_iff_saturation_eq (q.comap P.subtype))]
    rw [(isPrimitiveSubmodule_iff_saturation_eq q)] at hQ
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, hay⟩ := mem_saturation_iff (q.comap P.subtype) y |>.mp hy
      have hmem : a • (P.subtype y) ∈ q := by
        have := hay
        rwa [Submodule.mem_comap] at this
      have hsat : P.subtype y ∈ saturation q :=
        mem_saturation_iff q _ |>.mpr ⟨a, ha, hmem⟩
      rw [hQ] at hsat
      exact hsat
    · intro hy
      refine mem_saturation_iff (q.comap P.subtype) y |>.mpr ⟨1, one_ne_zero, ?_⟩
      rw [Submodule.mem_comap]
      simpa using hy

theorem comap_planeSubmoduleTransport {P : PrimitiveIsotropic L 2}
    (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule) (q : Submodule R L.obj.carrier)
    (hq : q ≤ P.toSubmodule) :
    (planeSubmoduleTransport δ q hq).comap P.toSubmodule.subtype =
      (q.comap P.toSubmodule.subtype).map (δ : ↥P.toSubmodule →ₗ[R] ↥P.toSubmodule) := by
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_comap, mem_planeSubmoduleTransport] at hy
    obtain ⟨z, hz⟩ := hy
    refine Submodule.mem_map.mpr ⟨Submodule.inclusion hq z, ?_, ?_⟩
    · rw [Submodule.mem_comap]
      exact z.2
    · exact Subtype.ext hz
  · intro hy
    rw [Submodule.mem_map] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    rw [Submodule.mem_comap, mem_planeSubmoduleTransport]
    refine ⟨⟨w.1, ?_⟩, ?_⟩
    · rw [Submodule.mem_comap] at hw
      exact hw
    · conv_lhs => rw [show Submodule.inclusion hq ⟨w.1, (by
          rw [Submodule.mem_comap] at hw; exact hw : w.1 ∈ q)⟩ = w from Subtype.ext rfl]
      simpa using hwy

theorem planeSubmoduleTransport_primitive [IsDomain R] {P : PrimitiveIsotropic L 2}
    (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule) (q : Submodule R L.obj.carrier)
    (hq : q ≤ P.toSubmodule) (hqP : IsPrimitiveSubmodule q) :
    IsPrimitiveSubmodule (planeSubmoduleTransport δ q hq) := by
  rw [← isPrimitiveSubmodule_comap_subtype_iff (planeSubmoduleTransport_le δ q hq) P.primitive,
    comap_planeSubmoduleTransport]
  exact (IsPrimitiveSubmodule.map_equiv_iff δ _).mpr
    ((isPrimitiveSubmodule_comap_subtype_iff hq P.primitive).mpr hqP)

/-- **The image of a primitive isotropic line under an equivalence of the plane**, as a primitive
isotropic line of `L` still lying in `P`. This is where the primitivity lives: `δ` is not an
automorphism of `L`, so `IsPrimitiveSubmodule.map_equiv_iff` cannot be applied to the line directly;
it is applied inside `P` after the sandwich `isPrimitiveSubmodule_comap_subtype_iff`. -/
noncomputable def planeLineTransport [IsDomain R] {P : PrimitiveIsotropic L 2}
    (δ : ↥(planeStabilizerImage P)) (q : PlaneLines L P) : PlaneLines L P :=
  ⟨{ toSubmodule := planeSubmoduleTransport (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
        q.1.toSubmodule q.2
     isotropic := planeSubmoduleTransport_isotropic _ _ _
     finrank_eq := planeSubmoduleTransport_finrank _ _ _ q.1.finrank_eq
     primitive := planeSubmoduleTransport_primitive _ _ _ q.1.primitive },
   planeSubmoduleTransport_le _ _ _⟩

/-- **The action of `Δ` on the incident lines is the action of the plane stabilizer read through
the image**: an element of `Δ` is the restriction of an ambient stabilizer element, and the
transported line is that element's translate. -/
theorem planeLineTransport_restrict_coe [IsDomain R] {P : PrimitiveIsotropic L 2}
    (g : ↥(MulAction.stabilizer (OrthogonalGroup L) P)) (q : PlaneLines L P)
    (hmem : planeStabilizerRestrict g ∈ planeStabilizerImage P) :
    (planeLineTransport (⟨planeStabilizerRestrict g, hmem⟩ :
      ↥(planeStabilizerImage P)) q).1.toSubmodule = (g • q).1.toSubmodule := by
  have h1 : (planeLineTransport (⟨planeStabilizerRestrict g, hmem⟩ : ↥(planeStabilizerImage P))
        q).1.toSubmodule =
      planeSubmoduleTransport (planeStabilizerRestrict g) q.1.toSubmodule q.2 := rfl
  have h2 : (g • q).1.toSubmodule =
      q.1.toSubmodule.map (g.1.1 : L.obj.carrier →ₗ[R] L.obj.carrier) := by
    simp only [PlaneLines.coe_smul]
    exact OrthogonalGroup.smul_submodule_eq_map g.1 q.1.toSubmodule
  rw [h1, h2]
  ext x
  rw [mem_planeSubmoduleTransport, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y.1, y.2, ?_⟩
    rw [← hy, planeStabilizerRestrict_apply_coe]
    rfl
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, planeStabilizerRestrict_apply_coe g _⟩

theorem planeSubmoduleTransport_one {P : PrimitiveIsotropic L 2}
    (q : Submodule R L.obj.carrier) (hq : q ≤ P.toSubmodule) :
    planeSubmoduleTransport (1 : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule) q hq = q := by
  ext x
  rw [mem_planeSubmoduleTransport]
  constructor
  · rintro ⟨y, hy⟩
    rw [show ((1 : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule) (Submodule.inclusion hq y) :
      ↥P.toSubmodule) = Submodule.inclusion hq y from rfl] at hy
    exact hy ▸ y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem planeSubmoduleTransport_mul {P : PrimitiveIsotropic L 2}
    (δ ε : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
    (q : Submodule R L.obj.carrier) (hq : q ≤ P.toSubmodule) :
    planeSubmoduleTransport (δ * ε) q hq =
      planeSubmoduleTransport δ (planeSubmoduleTransport ε q hq)
        (planeSubmoduleTransport_le ε q hq) := by
  ext x
  rw [mem_planeSubmoduleTransport]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨⟨(ε (Submodule.inclusion hq y) : ↥P.toSubmodule), ?_⟩, ?_⟩
    · rw [mem_planeSubmoduleTransport]
      exact ⟨y, rfl⟩
    · rw [show (δ * ε) (Submodule.inclusion hq y) =
        δ (ε (Submodule.inclusion hq y)) from rfl] at hy
      exact hy
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ : ∃ y : ↥q, ε (Submodule.inclusion hq y) =
        (⟨z.1, planeSubmoduleTransport_le ε q hq z.2⟩ : ↥P.toSubmodule) := by
      have h := z.2
      rw [mem_planeSubmoduleTransport] at h
      obtain ⟨y, hy⟩ := h
      exact ⟨y, Subtype.ext hy⟩
    refine ⟨y, ?_⟩
    rw [show (δ * ε) (Submodule.inclusion hq y) =
      δ (ε (Submodule.inclusion hq y)) from rfl, hy]
    exact hz

/-- **`Δ` acts on the incident primitive isotropic lines.** The action is the transport of the line
by the plane equivalence; `planeLineTransport` is where the primitivity of the image is proved, so
the action lands in `PlaneLines` and is not a function into the ambient line type. -/
noncomputable instance instSMulPlaneStabilizerImage [IsDomain R] {P : PrimitiveIsotropic L 2} :
    SMul ↥(planeStabilizerImage P) (PlaneLines L P) :=
  ⟨fun δ q => planeLineTransport δ q⟩

/-- The action of `Δ` on the incident lines is an action, with the laws transported through
`planeLineTransport`. -/
noncomputable instance instMulActionPlaneStabilizerImage [IsDomain R] {P : PrimitiveIsotropic L 2} :
    MulAction ↥(planeStabilizerImage P) (PlaneLines L P) where
  smul := fun δ q => planeLineTransport δ q
  one_smul q := by
    apply Subtype.ext
    apply PrimitiveIsotropic.ext
    exact planeSubmoduleTransport_one q.1.toSubmodule q.2
  mul_smul δ ε q := by
    apply Subtype.ext
    apply PrimitiveIsotropic.ext
    exact planeSubmoduleTransport_mul (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule)
      (ε : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule) q.1.toSubmodule q.2

/-- The incidence action of `Δ` is the transport of the underlying line. -/
theorem planeStabilizerImage.coe_smul [IsDomain R] {P : PrimitiveIsotropic L 2}
    (δ : ↥(planeStabilizerImage P)) (q : PlaneLines L P) :
    (δ • q : PlaneLines L P).1.toSubmodule =
      planeSubmoduleTransport (δ : ↥P.toSubmodule ≃ₗ[R] ↥P.toSubmodule) q.1.toSubmodule q.2 :=
  rfl

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
