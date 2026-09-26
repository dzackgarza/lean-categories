/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Order.KrullDimension

/-!
# Principal divisors on one-dimensional Noetherian domains

Definition-level realization of Neukirch FC09-C01-U115.

The source divisor of a nonzero rational function is the finite formal sum of
its codimension-one orders. The finite-support construction is ported from the
scheme-theoretic principal-divisor implementation in TauCetiProject/TauCeti,
AlgebraicGeometry/WeilDivisor/Scheme/Principal.lean.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Order TopologicalSpace

namespace LeanCategories.Algebra

universe u

/-- Codimension-one points of a scheme. -/
abbrev CodimensionOnePointData (X : Scheme.{u}) : Type u :=
  {x : X // coheight x = 1}

namespace CodimensionOnePointData

variable {X : Scheme.{u}}

/-- A maximal point of an irreducible space is its generic point. -/
private lemma eq_genericPoint_of_isMax [IrreducibleSpace X] {y : X} (hy : IsMax y) :
    y = genericPoint X :=
  Inseparable.eq <| inseparable_iff_specializes_and.mpr
    ⟨hy (genericPoint_specializes y), genericPoint_specializes y⟩

/-- A codimension-one point in the complement of a nonempty open equals the
generic point of the irreducible closed piece containing it. -/
private lemma eq_of_subset_compl_of_isGenericPoint [IrreducibleSpace X]
    {U : X.Opens} [Nonempty U] {T : Set X} (hTU : T ⊆ (U : Set X)ᶜ)
    {y : X} (hyGeneric : IsGenericPoint y T)
    {x : CodimensionOnePointData X} (hxT : (x : X) ∈ T) : (x : X) = y := by
  by_contra hne
  have hxylt : (x : X) < y := by
    refine ⟨hyGeneric.specializes hxT, ?_⟩
    intro hyx
    exact hne (Inseparable.eq <| inseparable_iff_specializes_and.mpr
      ⟨hyx, hyGeneric.specializes hxT⟩)
  have hyMax : IsMax y :=
    Order.coheight_eq_zero.mp <|
      Order.lt_one_iff.mp <| (Order.coheight_eq_coe_iff.mp x.property).2.2 y hxylt
  have hηU : genericPoint X ∈ U :=
    (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr <| by
      obtain ⟨u⟩ := (inferInstance : Nonempty U)
      exact ⟨u.1, Set.mem_univ _, u.property⟩
  exact hTU hyGeneric.mem ((eq_genericPoint_of_isMax hyMax).symm ▸ hηU)

/-- A nonempty open in a Noetherian irreducible scheme misses only finitely
many codimension-one points. -/
lemma finite_not_mem [IrreducibleSpace X] [NoetherianSpace X]
    (U : X.Opens) [Nonempty U] :
    {x : CodimensionOnePointData X | (x : X) ∉ U}.Finite := by
  obtain ⟨S, hSfinite, hSclosed, hSirreducible, hSunion⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let g : S → X := fun T ↦ (hSirreducible T T.property).genericPoint
  have hfiniteRange : (Set.range g).Finite := by
    let : Finite S := hSfinite.to_subtype
    exact Set.finite_range g
  apply Set.Finite.of_finite_image
  · refine hfiniteRange.subset ?_
    rintro _ ⟨x, hxU, rfl⟩
    have hxUnion : (x : X) ∈ ⋃₀ S := by
      rw [← hSunion]
      exact hxU
    obtain ⟨T, hTS, hxT⟩ := Set.mem_sUnion.mp hxUnion
    have hyGeneric : IsGenericPoint (g ⟨T, hTS⟩) T :=
      (hSirreducible T hTS).isGenericPoint_genericPoint (hSclosed T hTS)
    have hTcompl : T ⊆ (U : Set X)ᶜ := hSunion ▸ Set.subset_sUnion_of_mem hTS
    exact ⟨⟨T, hTS⟩, (eq_of_subset_compl_of_isGenericPoint hTcompl hyGeneric hxT).symm⟩
  · exact Set.injOn_of_injective Subtype.val_injective

end CodimensionOnePointData

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- Neukirch's local order coefficient at a codimension-one prime. -/
def localOrderCoefficientData
    (p : CodimensionOnePointData (Spec (.of A)))
    (f : (Spec (.of A)).functionFieldˣ) : ℤ :=
  (Spec (.of A)).ord (f : (Spec (.of A)).functionField) p

/-- The order coefficients of a nonzero rational function have finite support. -/
lemma finiteSupportLocalOrderCoefficientData
    (f : (Spec (.of A)).functionFieldˣ) :
    (Function.support fun p : CodimensionOnePointData (Spec (.of A)) ↦
      localOrderCoefficientData p f).Finite := by
  let X := Spec (.of A)
  obtain ⟨U, _, a, hU, ha, haUnit⟩ :=
    exists_isUnit_germ_eq X (f : X.functionField) (Units.ne_zero f)
  let : Nonempty U := hU
  refine (CodimensionOnePointData.finite_not_mem U).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq]
  intro hpU
  exact hp <| by
    simpa only [localOrderCoefficientData, ← ha] using X.ord_of_isUnit haUnit hpU

/-- Neukirch's principal divisor, constructed as an actual finitely supported
integer-valued function. -/
def principalDivisorData
    (f : (Spec (.of A)).functionFieldˣ) :
    CodimensionOnePointData (Spec (.of A)) →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun p ↦ localOrderCoefficientData p f)
    (finiteSupportLocalOrderCoefficientData f)

/-- Principal divisors as an intrinsic set-theoretic carrier. -/
def principalDivisorCarrierData :
    Set (CodimensionOnePointData (Spec (.of A)) →₀ ℤ) :=
  Set.range (principalDivisorData (A := A))

/-- Neukirch's rational equivalence relation: two divisors differ by a
principal divisor. -/
def RationallyEquivalentData
    (D E : CodimensionOnePointData (Spec (.of A)) →₀ ℤ) : Prop :=
  D - E ∈ principalDivisorCarrierData (A := A)

end LeanCategories.Algebra
