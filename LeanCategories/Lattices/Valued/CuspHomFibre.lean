/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CuspVector
public import LeanCategories.Lattices.Valued.DiscriminantAction
public import LeanCategories.Lattices.Valued.ScaleAndEvenness
public import LeanCategories.Modules.Quadratic.Valued.OrthogonalGroup

/-!
# The discriminant-class fibre theorem for a general homomorphism (#113)

`CuspVector` states the fibre theorem with range `ρ(O(L))` and never surjectivity. The issue wants
the stabilizer computed in the whole target group — `O(q_L)` — with `ρ` surjective. Rather than
transport quotients between the range and the whole target, this module states it for a general
homomorphism `σ : O(L) →* G` with `G` acting on the discriminant class's carrier, and derives
it from the same double-coset argument: `rangeLift` is replaced by a section of `σ`, which
exists exactly when `σ` is surjective. The theorem is therefore proved directly at the full
target.

For the bilinear discriminant representation that gives a theorem paralleling
`vectorFibreEquivStabilizer`; for the **quadratic** representation,
`OrthogonalGroup.evenDiscriminantRepresentation hL hEven` — a homomorphism of
`O(L)` into `O(q_L)` that for an even lattice preserves the quadratic form by
`evenDiscriminantQuadraticMap_actOnDefect` — it gives the statement #113 asks for.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R} [NoZeroSMulDivisors R L.obj.carrier]

section Hom

variable {G : Type u} {α : Type u} [Group G] [MulAction G α]
variable (σ : OrthogonalGroup L →* G) (v : PrimitiveIsotropicVector L) (c : α)
variable (hstab : ∀ s : OrthogonalGroup L, s ∈
  MulAction.stabilizer (OrthogonalGroup L) v → σ s • c = c)

/-- A section of a surjective `σ`. -/
noncomputable def sectionOfSurjective (hσ : Function.Surjective σ) : G → OrthogonalGroup L :=
  fun x => Classical.choose (hσ x)

theorem section_spec (hσ : Function.Surjective σ) (x : G) :
    σ (sectionOfSurjective σ hσ x) = x :=
  Classical.choose_spec (hσ x)

/-- The discriminant-class map associated to `σ`: `ker σ · g · Stab(v) ↦ σ(g)·c`. It is well
defined because `ker σ` acts trivially on the left and the stabilizer of `v` fixes `c` (that is
`hstab`). -/
noncomputable def classMap :
    DoubleCoset.Quotient (MonoidHom.ker σ : Set (OrthogonalGroup L))
      (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) → α :=
  Quotient.lift (fun g => σ g • c) (by
    intro a b hab
    obtain ⟨γ, hγ, h, hh, rfl⟩ := (DoubleCoset.rel_iff
      (H := (MonoidHom.ker σ))
      (K := MulAction.stabilizer (OrthogonalGroup L) v)).mp hab
    have hk : σ γ = 1 := hγ
    have hs : σ h • c = c := hstab h hh
    symm
    calc σ (γ * a * h) • c = (σ γ * σ a * σ h) • c := by rw [map_mul, map_mul]
      _ = ((1 * σ a) * σ h) • c := by rw [hk]
      _ = (σ a * σ h) • c := by rw [one_mul]
      _ = σ a • (σ h • c) := by rw [mul_smul]
      _ = σ a • c := by rw [hs])

omit [IsDomain R] [NoZeroSMulDivisors R L.obj.carrier] in
/-- Two lifts of `σ` whose images differ by an element of the stabilizer of `v` give the same
double coset: the conjugate-in-kernel computation, identical to
`doset_mk_eq_of_rangeRestrict_mul_vector` but for `σ` itself rather than its range restriction. -/
theorem doset_eq_of_apply_mul {x y s : OrthogonalGroup L}
    (hs : s ∈ MulAction.stabilizer (OrthogonalGroup L) v)
    (h : σ y = σ x * σ s) :
    DoubleCoset.mk (MonoidHom.ker σ)
        (MulAction.stabilizer (OrthogonalGroup L) v) x =
      DoubleCoset.mk (MonoidHom.ker σ)
        (MulAction.stabilizer (OrthogonalGroup L) v) y := by
  have hk : x⁻¹ * y * s⁻¹ ∈ (MonoidHom.ker σ) := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hγ : x * (x⁻¹ * y * s⁻¹) * x⁻¹ ∈ MonoidHom.ker σ :=
    (MonoidHom.normal_ker _).conj_mem _ hk x
  rw [DoubleCoset.eq]
  exact ⟨_, hγ, s, hs, by group⟩

/-- The map from stabilizer cosets of the class in `G` to the fibre, defined on the quotient by the
image of the stabilizer of the vector under `σ`. -/
noncomputable def stabilizerCosetsToFibre (hσ : Function.Surjective σ) :
    MulAction.stabilizer G c ⧸
      ((MulAction.stabilizer (OrthogonalGroup L) v).map σ).subgroupOf
        (MulAction.stabilizer G c) →
      {q : DoubleCoset.Quotient (MonoidHom.ker σ : Set (OrthogonalGroup L))
        (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) //
        classMap σ v c hstab q = c} :=
  Quotient.lift (fun x : MulAction.stabilizer G c =>
    ⟨DoubleCoset.mk _ _ (sectionOfSurjective σ hσ x.1), by
      show σ (sectionOfSurjective σ hσ x.1) • c = c
      rw [section_spec]
      exact x.2⟩) (by
    intro a b hrel
    obtain ⟨s, hs, hes⟩ := Subgroup.mem_map.mp
      (Subgroup.mem_subgroupOf.mp ((QuotientGroup.leftRel_apply).mp hrel))
    apply Subtype.ext
    have hp : σ (sectionOfSurjective σ hσ b.1) =
        σ (sectionOfSurjective σ hσ a.1) * σ s := by
      have hmem : σ s = a.1⁻¹ * b.1 := by
        rw [hes, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [section_spec σ hσ b.1, section_spec σ hσ a.1, hmem, mul_inv_cancel_left]
    exact doset_eq_of_apply_mul σ v hs hp)

/-- Injective: cosets mapping to the same fibre element have the same class. -/
theorem stabilizerCosetsToFibre_injective (hσ : Function.Surjective σ) :
    Function.Injective (stabilizerCosetsToFibre σ v c hstab hσ) := by
  intro A B hxy
  induction A using Quotient.inductionOn with
  | _ a =>
  induction B using Quotient.inductionOn with
  | _ b =>
  obtain ⟨γ, hγ, s, hs, hrel⟩ :=
    (DoubleCoset.eq (MonoidHom.ker σ)
      (MulAction.stabilizer (OrthogonalGroup L) v)
      (sectionOfSurjective σ hσ a.1) (sectionOfSurjective σ hσ b.1)).mp
      (congrArg Subtype.val hxy)
  have hk : σ γ = 1 := hγ
  have hb : b.1 = a.1 * σ s := by
    have h1 : σ (sectionOfSurjective σ hσ b.1) = b.1 := section_spec σ hσ b.1
    have h2 : σ (sectionOfSurjective σ hσ a.1) = a.1 := section_spec σ hσ a.1
    rw [← h1, ← h2, hrel, map_mul, map_mul, hk, one_mul]
  have hcoe : ((a⁻¹ * b : MulAction.stabilizer G c) :
        ↥(MulAction.stabilizer G c)) = a.1⁻¹ * b.1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  refine ⟨s, hs, ?_⟩
  rw [hcoe, hb, inv_mul_cancel_left a.1 (σ s)]

/-- Surjective: every fibre element is the image of a stabilizer coset, represented by the section
of a general element. -/
theorem stabilizerCosetsToFibre_surjective (hσ : Function.Surjective σ) :
    Function.Surjective (stabilizerCosetsToFibre σ v c hstab hσ) := by
  rintro ⟨⟨g⟩, hd⟩
  have hg : σ g ∈ MulAction.stabilizer G c := hd
  refine ⟨QuotientGroup.mk ⟨σ g, hg⟩, ?_⟩
  apply Subtype.ext
  have hone : σ g = σ (sectionOfSurjective σ hσ (σ g)) * σ (1 : OrthogonalGroup L) := by
    rw [section_spec, map_one, mul_one]
  exact doset_eq_of_apply_mul σ v (Subgroup.one_mem _) hone

/-- **The discriminant-class fibre theorem at the full target** (#113): for a surjective `σ`, the
fibre of `ker σ·g·Stab(v) ↦ σ(g)·c` over the class `c` is the stabilizer of `c` in `G` modulo
the image of the stabilizer of the *vector* under `σ`. -/
noncomputable def vectorFibreEquivStabilizerSurjective (hσ : Function.Surjective σ) :
    {q : DoubleCoset.Quotient (MonoidHom.ker σ : Set (OrthogonalGroup L))
        (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) //
      classMap σ v c hstab q = c} ≃
      MulAction.stabilizer G c ⧸
        ((MulAction.stabilizer (OrthogonalGroup L) v).map σ).subgroupOf
          (MulAction.stabilizer G c) :=
  (Equiv.ofBijective (stabilizerCosetsToFibre σ v c hstab hσ)
    ⟨stabilizerCosetsToFibre_injective σ v c hstab hσ,
      stabilizerCosetsToFibre_surjective σ v c hstab hσ⟩).symm

end Hom


section Quadratic

variable (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)

/-- The quadratic discriminant module of an even lattice: the module that `O(q_L)` acts on. -/
noncomputable abbrev quadraticDiscriminantCarrier :=
  (evenDiscriminantQuadraticObject L hL hEven).carrier

/-- The class of `v/div(v)` in the quadratic discriminant module. -/
noncomputable def quadraticDiscriminantClass {v : PrimitiveIsotropicVector L}
    (D : PrimitiveIsotropicVector.DivisibilityData v) : quadraticDiscriminantCarrier hL hEven :=
  PrimitiveIsotropicVector.discriminantClass D

/-- Stabilizers of a vector fix the class: `actOnEvenDiscriminantQuadraticForm` is the same map as
`actOnDefect`, so the fact `fixes_discriminantClass` proved for the bilinear action applies
verbatim, only read in the quadratic discriminant module. -/
theorem quadratic_stabilizer_fixes_discriminantClass {v : PrimitiveIsotropicVector L}
    (D : PrimitiveIsotropicVector.DivisibilityData v) {h : OrthogonalGroup L}
    (hfix : h • v = v) :
    OrthogonalGroup.evenDiscriminantRepresentation hL hEven h •
      quadraticDiscriminantClass hL hEven D =
      quadraticDiscriminantClass hL hEven D :=
  PrimitiveIsotropicVector.fixes_discriminantClass hL D hfix

set_option maxHeartbeats 1200000 in
-- instantiation of the big `DoubleCoset.Quotient`/`subgroupOf` type re-runs instance search through
-- the discriminant bilinear object, exactly as in the range version of the fibre theorem
/-- **The quadratic-discriminant-class fibre theorem at the full target** (#113): for an even
lattice `L` with `ρ : O(L) →* O(q_L)` the quadratic discriminant representation, a primitive
isotropic vector `v`, a class `c` of the quadratic discriminant module fixed by `ρ(Stab_{O(L)}(v))`
(`hstab` — for `c = [v/d]` this is `quadratic_stabilizer_fixes_discriminantClass`), assume `ρ` is
**surjective**. Then the fibre of the class map
`ker ρ · g · Stab(v) ↦ ρ(g)·c` over `c` is the stabilizer of `c` **in `O(q_L)`** modulo the
image of the stabilizer of the vector under `ρ`.

The class is taken as a parameter rather than derived from divisibility data: the fibre statement
only consumes `c` and `hstab`, so a worked instance may supply its class by any proved route. -/
noncomputable def vectorFibreEquivQuadraticSurjective
    (v : PrimitiveIsotropicVector L) (c : quadraticDiscriminantCarrier hL hEven)
    (hstab : ∀ s : OrthogonalGroup L, s ∈ MulAction.stabilizer (OrthogonalGroup L) v →
      OrthogonalGroup.evenDiscriminantRepresentation hL hEven s • c = c)
    (hσ : Function.Surjective (OrthogonalGroup.evenDiscriminantRepresentation hL hEven)) :
    {q : DoubleCoset.Quotient ((MonoidHom.ker
          (OrthogonalGroup.evenDiscriminantRepresentation hL hEven)) : Set (OrthogonalGroup L))
        (MulAction.stabilizer (OrthogonalGroup L) v : Set (OrthogonalGroup L)) //
      classMap (OrthogonalGroup.evenDiscriminantRepresentation hL hEven) v c hstab q = c} ≃
      MulAction.stabilizer (QuadModuleCat.OrthogonalGroup
          (evenDiscriminantQuadraticObject L hL hEven)) c ⧸
        ((MulAction.stabilizer (OrthogonalGroup L) v).map
          (OrthogonalGroup.evenDiscriminantRepresentation hL hEven)).subgroupOf
          (MulAction.stabilizer (QuadModuleCat.OrthogonalGroup
            (evenDiscriminantQuadraticObject L hL hEven)) c) :=
  vectorFibreEquivStabilizerSurjective
    (OrthogonalGroup.evenDiscriminantRepresentation hL hEven) v c hstab hσ

end Quadratic

end LeanCategories.Lattices.Valued
