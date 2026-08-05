module

public import LeanCategories.Lattices.Integral.Unbundled.Basic

@[expose] public section

namespace LeanCategories.Modules.Quadratic

open LeanCategories.Lattices.Integral.Unbundled

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

structure Isometry (B1 : LinearMap.BilinForm R M) (B2 : LinearMap.BilinForm R N) extends M ≃ₗ[R] N where
  map_app : ∀ x y : M, B2 (toFun x) (toFun y) = B1 x y

end LeanCategories.Modules.Quadratic
