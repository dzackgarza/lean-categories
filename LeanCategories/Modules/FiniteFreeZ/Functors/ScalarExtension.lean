module

public import LeanCategories.Modules.FiniteFreeZ.Objects.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

namespace LeanCategories.Modules.FiniteFreeZ

open CategoryTheory

/-- Rationalization: M ⊗_Z ℚ. -/
abbrev Rationalization (M : ZLat) : Type _ :=
  TensorProduct ℤ ℚ M.carrier

instance (M : ZLat) : AddCommGroup (Rationalization M) :=
  inferInstance

instance (M : ZLat) : Module ℚ (Rationalization M) :=
  inferInstance

/-- Realification: M ⊗_Z ℝ. -/
abbrev Realification (M : ZLat) : Type _ :=
  TensorProduct ℤ ℝ M.carrier

instance (M : ZLat) : AddCommGroup (Realification M) :=
  inferInstance

instance (M : ZLat) : Module ℝ (Realification M) :=
  inferInstance

/-- Scalar extension of a lattice map to rational vector spaces. -/
axiom rationalizedMap {M N : ZLat} (f : M ⟶ N) :
    Rationalization M →ₗ[ℚ] Rationalization N

axiom rationalizedMap_id (M : ZLat) : rationalizedMap (𝟙 M) = LinearMap.id

axiom rationalizedMap_comp {L M N : ZLat} (f : L ⟶ M) (g : M ⟶ N) :
    rationalizedMap (f ≫ g) = (rationalizedMap g).comp (rationalizedMap f)

/-- Rational scalar extension as an actual category-theoretic functor. -/
noncomputable def rationalizationFunctor : ZLat ⥤ ModuleCat ℚ where
  obj M := ModuleCat.of ℚ (Rationalization M)
  map f := ModuleCat.ofHom (rationalizedMap f)
  map_id M := by ext; exact LinearMap.congr_fun (rationalizedMap_id M) _
  map_comp f g := by ext; exact LinearMap.congr_fun (rationalizedMap_comp f g) _

/-- Scalar extension of a lattice map to real vector spaces. -/
axiom realifiedMap {M N : ZLat} (f : M ⟶ N) : Realification M →ₗ[ℝ] Realification N

axiom realifiedMap_id (M : ZLat) : realifiedMap (𝟙 M) = LinearMap.id

axiom realifiedMap_comp {L M N : ZLat} (f : L ⟶ M) (g : M ⟶ N) :
    realifiedMap (f ≫ g) = (realifiedMap g).comp (realifiedMap f)

/-- Real scalar extension as an actual category-theoretic functor. -/
noncomputable def realificationFunctor : ZLat ⥤ ModuleCat ℝ where
  obj M := ModuleCat.of ℝ (Realification M)
  map f := ModuleCat.ofHom (realifiedMap f)
  map_id M := by ext; exact LinearMap.congr_fun (realifiedMap_id M) _
  map_comp f g := by ext; exact LinearMap.congr_fun (realifiedMap_comp f g) _

/-- Canonical map M → M ⊗_Z ℚ sending m ↦ m ⊗ 1. -/
axiom rationalizationMap (M : ZLat) : M.carrier →ₗ[ℤ] Rationalization M

/-- Canonical map M → M ⊗_Z ℝ sending m ↦ m ⊗ 1. -/
axiom realificationMap (M : ZLat) : M.carrier →ₗ[ℤ] Realification M

/-- The rationalization of a free Z-module is a ℚ-vector space of the same dimension. -/
axiom rationalizationFinrank (M : ZLat) :
    Module.finrank ℚ (Rationalization M) = Module.finrank ℤ M.carrier

end LeanCategories.Modules.FiniteFreeZ
