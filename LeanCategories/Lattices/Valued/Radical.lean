/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Basic

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- The radical lies in the left kernel of the lattice form. -/
theorem radical_le_bilinMap_ker (L : IntegralLatticeCat R) :
    L.obj.radical ≤ LinearMap.ker L.obj.bilinMap := by
  intro x hx
  exact hx

/-- Symmetry puts the radical in the right kernel of the lattice form. -/
theorem radical_le_bilinMap_flip_ker (L : IntegralLatticeCat R) :
    L.obj.radical ≤ LinearMap.ker L.obj.bilinMap.flip := by
  intro x hx
  rw [BilinModuleCat.radical, LinearMap.mem_ker] at hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change L.obj.pairing y x = 0
  rw [L.property.2 y x]
  change L.obj.bilinMap x y = 0
  rw [hx]
  rfl

/-- The form induced on the quotient by the radical. -/
def radicalQuotientBilinMap (L : IntegralLatticeCat R) :
    LinearMap.BilinMap R (L.obj.carrier ⧸ L.obj.radical) R :=
  L.obj.bilinMap.liftQ₂ L.obj.radical L.obj.radical
    (radical_le_bilinMap_ker L)
    (radical_le_bilinMap_flip_ker L)

/-- The formed module obtained after quotienting a lattice by its radical. -/
def radicalQuotient (L : IntegralLatticeCat R) : BilinModuleCat R R :=
  BilinModuleCat.ofBilinMap (radicalQuotientBilinMap L)

@[simp]
theorem radicalQuotient_pairing_mk (L : IntegralLatticeCat R)
    (x y : L.obj.carrier) :
    (radicalQuotient L).pairing
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
        L.obj.pairing x y :=
  rfl

/-- The quotient by the radical remains symmetric. -/
theorem radicalQuotient_isSymmetric (L : IntegralLatticeCat R) :
    (radicalQuotient L).IsSymmetric := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
          exact L.property.2 x y

/-- Quotienting by the radical gives a nondegenerate formed module. -/
theorem radicalQuotient_isNondegenerate (L : IntegralLatticeCat R) :
    (radicalQuotient L).IsNondegenerate := by
  rw [BilinModuleCat.isNondegenerate_iff_adjoint_injective]
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Quotient.inductionOn with
  | _ x =>
      change (Submodule.Quotient.mk x :
        L.obj.carrier ⧸ L.obj.radical) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      rw [BilinModuleCat.radical, LinearMap.mem_ker]
      apply LinearMap.ext
      intro y
      have hxy := LinearMap.congr_fun hx (Submodule.Quotient.mk y)
      change (radicalQuotient L).pairing
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = 0 at hxy
      rw [radicalQuotient_pairing_mk] at hxy
      change L.obj.pairing x y = 0
      exact hxy

end LeanCategories.Lattices.Valued
