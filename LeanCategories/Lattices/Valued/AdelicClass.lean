/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Adele
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Finite adelic classes of integral lattices

The ambient quadratic space is first extended from the integer ring to its number field.
Its orthogonal group is then extended to the finite adele ring. This presentation gives the
diagonal rational subgroup without a choice of basis.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open LeanCategories.Modules.Bilinear.Valued
open scoped NumberField
open scoped Pointwise

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The rational quadratic space attached to an integral lattice. -/
abbrev NumberFieldRationalLattice
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  (baseChangeIntegral (𝓞 K) K).obj L.obj

/-- The rational orthogonal group of an integral lattice. -/
abbrev RationalOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup (NumberFieldRationalLattice K L).obj

/-- The finite adelic orthogonal group of the rational quadratic space. -/
abbrev RationalFiniteAdelicOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup
    ((baseChangeIntegral K (FiniteAdeleRing (𝓞 K) K)).obj
      (NumberFieldRationalLattice K L)).obj

/-- Scalar extension gives the diagonal rational subgroup in the finite adelic group. -/
noncomputable def rationalFiniteAdeleOrthogonalHom
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    RationalOrthogonalGroup K L →*
      RationalFiniteAdelicOrthogonalGroup K L :=
  orthogonalGroupBaseChangeHom (R := K) (FiniteAdeleRing (𝓞 K) K)
    (NumberFieldRationalLattice K L)

/-- The image of the rational orthogonal group under the diagonal map. -/
abbrev RationalFiniteAdeleOrthogonalSubgroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Subgroup (RationalFiniteAdelicOrthogonalGroup K L) :=
  (rationalFiniteAdeleOrthogonalHom K L).range

/-- The finite adelic orthogonal group acts on its quadratic space. -/
instance rationalFiniteAdelicOrthogonalGroupMulAction
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    MulAction (RationalFiniteAdelicOrthogonalGroup K L)
      ((baseChangeIntegral K (FiniteAdeleRing (𝓞 K) K)).obj
        (NumberFieldRationalLattice K L)).obj.carrier where
  smul g x := g.1 x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The integral finite adelic lattice inside the adelization of the rational space. -/
def rationalFiniteIntegralAdeleLattice
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Set ((baseChangeIntegral K (FiniteAdeleRing (𝓞 K) K)).obj
      (NumberFieldRationalLattice K L)).obj.carrier :=
  Set.range fun x :
      TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier =>
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (𝓞 K) K (FiniteAdeleRing (𝓞 K) K)
      (FiniteAdeleRing (𝓞 K) K) L.obj.obj.carrier).symm
        (finiteIntegralAdeleLatticeMap K L x)

/-- The stabilizer of the integral finite adelic lattice. -/
abbrev RationalFiniteIntegralAdeleLatticeStabilizer
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  MulAction.stabilizer (RationalFiniteAdelicOrthogonalGroup K L)
    (rationalFiniteIntegralAdeleLattice K L)

/-- The finite adelic class space `O(V)(K) \ O(V)(𝔸_f) / K_L`. -/
abbrev FiniteAdelicClassSpace
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  DoubleCoset.Quotient
    (RationalFiniteAdeleOrthogonalSubgroup K L :
      Set (RationalFiniteAdelicOrthogonalGroup K L))
    (RationalFiniteIntegralAdeleLatticeStabilizer K L :
      Set (RationalFiniteAdelicOrthogonalGroup K L))

end LeanCategories.Lattices.Valued
