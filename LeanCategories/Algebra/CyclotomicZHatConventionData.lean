/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.AbstractNormalizedDegreeData
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Cyclotomic Z-hat convention data

Definition-level realization of Neukirch FC09-C06-U043.

The preceding source proposition identifies the chosen cyclotomic fixed field
as a `Z-hat`-extension.  Sweep III does not re-prove that result.  This file
records only the conventions and constructions that follow from making such a
choice: the resulting degree map, the field intersection and compositum, the
already-owned normalized-degree formula, and the distinguished element mapping
to the additive generator `1 ∈ Z-hat`.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w

/-- The chosen continuous degree map obtained from a fixed identification of
the cyclotomic `Z-hat` Galois group with `Z-hat`.

Surjectivity is a property of the source construction, not constructor data. -/
abbrev CyclotomicZHatDegreeChoiceData
    (G : Type u) [Group G] [TopologicalSpace G] :=
  G →ₜ* serreProfiniteIntegerData

/-- The field `K ∩ Q-tilde` inside a common ambient extension. -/
def cyclotomicZHatIntersectionData
    {F : Type u} {Ω : Type v}
    [Field F] [Field Ω] [Algebra F Ω]
    (K Qtilde : IntermediateField F Ω) :
    IntermediateField F Ω :=
  K ⊓ Qtilde

/-- Neukirch's finite intersection degree
`f_K = [K ∩ Q-tilde : Q]`.

The `FiniteDimensional` input is the source's finiteness condition inherited
from the assumption that `K/F` is finite. -/
def cyclotomicZHatIntersectionDegreeData
    {F : Type u} {Ω : Type v}
    [Field F] [Field Ω] [Algebra F Ω]
    (K Qtilde : IntermediateField F Ω)
    [FiniteDimensional F (cyclotomicZHatIntersectionData K Qtilde)] : ℕ :=
  Module.finrank F (cyclotomicZHatIntersectionData K Qtilde)

/-- The compositum `K Q-tilde` inside a common ambient extension. -/
def cyclotomicZHatCompositumData
    {F : Type u} {Ω : Type v}
    [Field F] [Field Ω] [Algebra F Ω]
    (K Qtilde : IntermediateField F Ω) :
    IntermediateField F Ω :=
  K ⊔ Qtilde

/-- The element of multiplicative `Z-hat` corresponding to additive
`1 ∈ Z-hat`. -/
def profiniteIntegerAdditiveGeneratorData :
    serreProfiniteIntegerData :=
  ProfiniteGrp.ProfiniteCompletion.etaFn
    (GrpCat.of (Multiplicative ℤ))
    (Multiplicative.ofAdd (1 : ℤ))

/-- Raw distinguished Frobenius for a supplied degree map: choose a preimage
of the additive generator `1 ∈ Z-hat`.

The source has a unique such element because its degree map is an isomorphism
on the cyclotomic Galois group.  Existence, uniqueness, and the equation
`d(φ)=1` are result-layer facts; `Function.invFun` records the selected
datum without proving them. -/
def distinguishedCyclotomicFrobeniusData
    {G : Type w} [Group G]
    (d : G → serreProfiniteIntegerData) : G :=
  Function.invFun d profiniteIntegerAdditiveGeneratorData

/-- Restriction of the distinguished cyclotomic Frobenius to a supplied finite
subextension. -/
def restrictedCyclotomicFrobeniusData
    {G : Type w} {H : Type v} [Group G]
    (restriction : G → H)
    (d : G → serreProfiniteIntegerData) : H :=
  restriction (distinguishedCyclotomicFrobeniusData d)

/-- Neukirch's source-exact normalized-degree formula
`d_K = (1/f_K)d`, with
`f_K = [K ∩ Q-tilde : F]`.

The division operation is reused from the accepted generic normalized-degree
owner.  That this raw division lands on the intended quotient and defines a
continuous surjective homomorphism is result content. -/
def cyclotomicNormalizedDegreeData
    {G : Type w} {F : Type u} {Ω : Type v}
    [Field F] [Field Ω] [Algebra F Ω]
    (d : G → serreProfiniteIntegerData)
    (K Qtilde : IntermediateField F Ω)
    [FiniteDimensional F (cyclotomicZHatIntersectionData K Qtilde)] :
    G → serreProfiniteIntegerData :=
  fun g =>
    profiniteIntegerDivNatData
      (cyclotomicZHatIntersectionDegreeData K Qtilde)
      (d g)

end LeanCategories.Algebra
