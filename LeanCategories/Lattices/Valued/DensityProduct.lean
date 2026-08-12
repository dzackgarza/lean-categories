/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.RestrictedProductMeasure
public import LeanCategories.Lattices.Valued.AdelicSpinorNorm

/-!
# The product of the local densities

The finite adelic orthogonal group of a lattice is the restricted product of the local
orthogonal groups with respect to the local integral subgroups. Those integral subgroups are
compact and open, so the restricted product carries a Haar measure normalized so that the
integral adelic orthogonal subgroup has measure one.

With that normalization the volume of a level subgroup, that is a family of local open
subgroups inside the integral ones which is integral at almost every place, is the product over
all finite places of the local volume divided by the local density. The product is finite
because almost all of its factors are one.

This is the measure-theoretic factorization that a Siegel mass formula consumes. The mass
formula itself is NOT stated here: it needs the volume of a quotient by the rational orthogonal
group, which compares the adelic Haar measure with a global lattice-counting measure, and no
such comparison is proved in this repository.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain MeasureTheory NumberField
open LeanCategories.ForMathlib LeanCategories.Modules.Bilinear.Valued
open scoped ENNReal NumberField RestrictedProduct

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [NumberField K]
variable (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))

/-! ## Measurable and topological structure -/

/-- The local integral orthogonal subgroups are open at every finite place. -/
instance localIntegralOrthogonalSubgroupOpen :
    Fact (∀ w : HeightOneSpectrum (𝓞 K),
      IsOpen (LocalIntegralOrthogonalSubgroup K w L :
        Set (LocalOrthogonalGroup K w L))) :=
  ⟨fun w => isOpen_localIntegralOrthogonalSubgroup K w L⟩

/-- The Borel measurable structure of a local orthogonal group. -/
instance localOrthogonalGroupMeasurableSpace (w : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (LocalOrthogonalGroup K w L) :=
  borel _

instance localOrthogonalGroupBorelSpace (w : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (LocalOrthogonalGroup K w L) :=
  ⟨rfl⟩

/-- The Borel measurable structure of the finite adelic orthogonal group. -/
instance adelicOrthogonalGroupMeasurableSpace :
    MeasurableSpace (AdelicOrthogonalGroup K L) :=
  borel _

instance adelicOrthogonalGroupBorelSpace : BorelSpace (AdelicOrthogonalGroup K L) :=
  ⟨rfl⟩

/-- The local Haar measure is a Haar measure. -/
instance localHaarMeasureIsHaarMeasure (w : HeightOneSpectrum (𝓞 K)) :
    (localHaarMeasure K w L).IsHaarMeasure := by
  dsimp only [localHaarMeasure, orthogonalGroupHaarMeasure]
  infer_instance

/-! ## The integral adelic orthogonal subgroup and its Haar measure -/

/-- The integral adelic orthogonal subgroup: the adelic isometries that are integral at every
finite place. -/
abbrev AdelicIntegralOrthogonalSubgroup : Subgroup (AdelicOrthogonalGroup K L) :=
  piSubgroup (fun w => LocalIntegralOrthogonalSubgroup K w L)
    fun w => LocalIntegralOrthogonalSubgroup K w L

/-- The integral adelic orthogonal subgroup is open. -/
theorem isOpen_adelicIntegralOrthogonalSubgroup :
    IsOpen (AdelicIntegralOrthogonalSubgroup K L : Set (AdelicOrthogonalGroup K L)) :=
  isOpen_piSubgroup (fun _ => le_rfl)
    (fun w => isOpen_localIntegralOrthogonalSubgroup K w L) (by simp)

/-- The integral adelic orthogonal subgroup is compact. -/
theorem isCompact_adelicIntegralOrthogonalSubgroup :
    IsCompact (AdelicIntegralOrthogonalSubgroup K L : Set (AdelicOrthogonalGroup K L)) :=
  isCompact_piSubgroup_self fun w => isCompact_localIntegralOrthogonalSubgroup K w L

/-- Haar measure on the finite adelic orthogonal group, normalized so that the integral adelic
orthogonal subgroup has measure one. -/
def adelicOrthogonalHaarMeasure : Measure (AdelicOrthogonalGroup K L) :=
  restrictedProductHaarMeasure fun w => isCompact_localIntegralOrthogonalSubgroup K w L

instance adelicOrthogonalHaarMeasureIsHaarMeasure :
    (adelicOrthogonalHaarMeasure K L).IsHaarMeasure :=
  isHaarMeasure_restrictedProductHaarMeasure _

/-- The integral adelic orthogonal subgroup has volume one. -/
@[simp]
theorem adelicOrthogonalHaarMeasure_integral :
    adelicOrthogonalHaarMeasure K L (AdelicIntegralOrthogonalSubgroup K L) = 1 :=
  restrictedProductHaarMeasure_self _

/-! ## The product formula -/

/-- The local density is the local Haar volume of the local integral orthogonal subgroup. -/
theorem localDensity_eq_localHaarMeasure (w : HeightOneSpectrum (𝓞 K)) :
    localDensity K w L = localHaarMeasure K w L (LocalIntegralOrthogonalSubgroup K w L) :=
  rfl

/-- **The volume of a level subgroup is the product of the local densities, normalized.** A
family `M` of open subgroups of the local orthogonal groups, contained in the local integral
subgroups and equal to them at almost every finite place, cuts out a compact open subgroup of
the finite adelic orthogonal group. Its volume, for the Haar measure normalized by the integral
adelic orthogonal subgroup, is the product over all finite places of the local volume of `M w`
divided by the local density. Almost every factor is one, so the product is finite. -/
theorem adelicOrthogonalHaarMeasure_piSubgroup
    (M : ∀ w : HeightOneSpectrum (𝓞 K), Subgroup (LocalOrthogonalGroup K w L))
    (hM : ∀ w, M w ≤ LocalIntegralOrthogonalSubgroup K w L)
    (hMopen : ∀ w, IsOpen (M w : Set (LocalOrthogonalGroup K w L)))
    (hS : {w | M w ≠ LocalIntegralOrthogonalSubgroup K w L}.Finite) :
    adelicOrthogonalHaarMeasure K L
        (piSubgroup (fun w => LocalIntegralOrthogonalSubgroup K w L) M) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 K),
        localHaarMeasure K w L (M w) / localDensity K w L :=
  restrictedProductHaarMeasure_piSubgroup _ (fun w => localHaarMeasure K w L) hM hMopen hS

end LeanCategories.Lattices.Valued
