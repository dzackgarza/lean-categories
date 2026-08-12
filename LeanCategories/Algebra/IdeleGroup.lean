/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.RestrictedProduct.Units
public import Mathlib.Topology.Algebra.Group.Units
public import LeanCategories.ForMathlib.AdicCompletionLocallyCompact
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Algebra.Group.Subgroup.Even

/-!
# Ideles of a number field

The idele topology is the product topology at infinite places and the restricted-product topology
on local unit groups at finite places. It is not the subspace topology on the units of the adele
ring.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField RestrictedProduct

namespace LeanCategories

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The product of the multiplicative groups at all infinite places. -/
abbrev InfiniteIdeleGroup :=
  (v : InfinitePlace K) → (v.Completion)ˣ

/-- The restricted product of finite local multiplicative groups with respect to local units. -/
abbrev FiniteIdeleGroup :=
  Πʳ v : HeightOneSpectrum (𝓞 K),
    [(v.adicCompletion K)ˣ,
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units]

/-- The idele group with its standard restricted-product topology. -/
abbrev IdeleGroup := InfiniteIdeleGroup K × FiniteIdeleGroup K

/-- Local integral unit groups are open in local multiplicative groups. -/
instance finiteIdeleOpenSubgroups : Fact (∀ v : HeightOneSpectrum (𝓞 K),
    IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ)) :=
  ⟨fun v => Submonoid.isOpen_units
    (show IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) from
      Valued.isOpen_valuationSubring (v.adicCompletion K))⟩

/-- The finite idele group is locally compact. -/
instance finiteIdeleGroupLocallyCompactSpace :
    LocallyCompactSpace (FiniteIdeleGroup K) := by
  letI (v : HeightOneSpectrum (𝓞 K)) :
      LocallyCompactSpace (v.adicCompletion K) :=
    HeightOneSpectrum.locallyCompactSpaceAdicCompletion K v
  letI (v : HeightOneSpectrum (𝓞 K)) :
      CompactSpace (v.adicCompletionIntegers K) :=
    HeightOneSpectrum.compactSpaceAdicCompletionIntegers K v
  apply RestrictedProduct.locallyCompactSpace_of_group
  filter_upwards [] with v
  exact (Submonoid.units_isCompact <|
    isCompact_iff_compactSpace.mpr
      (HeightOneSpectrum.compactSpaceAdicCompletionIntegers K v))

/-- The idele group is locally compact. -/
instance ideleGroupLocallyCompactSpace : LocallyCompactSpace (IdeleGroup K) :=
  inferInstance

/-- Haar measure on the idele group. -/
noncomputable def ideleHaarMeasure :
    @MeasureTheory.Measure (IdeleGroup K) (borel (IdeleGroup K)) := by
  letI : MeasurableSpace (IdeleGroup K) := borel _
  letI : BorelSpace (IdeleGroup K) := ⟨rfl⟩
  exact MeasureTheory.Measure.haar

/-- Algebraically, ideles are the units of the adele ring. This equivalence does not identify
the idele topology with the subspace topology on adele units. -/
def adeleUnitsEquivIdeleGroup :
    (AdeleRing (𝓞 K) K)ˣ ≃* IdeleGroup K :=
  MulEquiv.prodUnits |>.trans <|
    MulEquiv.prodCongr MulEquiv.piUnits <|
      RestrictedProduct.unitsEquiv
        (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)

/-- The diagonal embedding of nonzero field elements as principal ideles. -/
def principalIdele : Kˣ →* IdeleGroup K :=
  adeleUnitsEquivIdeleGroup K |>.toMonoidHom.comp <|
    Units.map (algebraMap K (AdeleRing (𝓞 K) K))

/-- The principal idele map is injective. -/
theorem principalIdele_injective : Function.Injective (principalIdele K) := by
  apply (adeleUnitsEquivIdeleGroup K).injective.comp
  exact Units.map_injective <| NumberField.AdeleRing.algebraMap_injective
    (𝓞 K) K

/-- The subgroup of principal ideles. -/
abbrev PrincipalIdeleSubgroup : Subgroup (IdeleGroup K) :=
  (principalIdele K).range

/-- The idele class group, modulo diagonally embedded field units. -/
abbrev IdeleClassGroup := IdeleGroup K ⧸ PrincipalIdeleSubgroup K

/-- The square-class group of the ideles. -/
abbrev IdeleSquareClass := IdeleGroup K ⧸ Subgroup.square (IdeleGroup K)

/-- The quotient map from ideles to idele square classes. -/
def ideleSquareClass : IdeleGroup K →* IdeleSquareClass K :=
  QuotientGroup.mk' (Subgroup.square (IdeleGroup K))

/-- Principal ideles define idele square classes. -/
def principalIdeleSquareClass : Kˣ →* IdeleSquareClass K :=
  (ideleSquareClass K).comp (principalIdele K)

end LeanCategories
