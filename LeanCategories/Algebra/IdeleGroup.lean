/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.RestrictedProduct.Units

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

/-- The subgroup of principal ideles. -/
abbrev PrincipalIdeleSubgroup : Subgroup (IdeleGroup K) :=
  (principalIdele K).range

end LeanCategories
