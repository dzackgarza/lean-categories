/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildEnveloping

/-!
# Square-zero Hochschild extensions and factor-set data

Weibel, *An Introduction to Homological Algebra* (1994), §9.3, pp. 311--318,
FC05-C09-U026.

Only the definition layer is recorded here. The cocycle identity for a factor
set, the coboundary formula for changing splittings, and the classification by
`HH²` are theorem-layer statements.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v w z

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module R M] [Module Rᵐᵒᵖ M]

/-- A square-zero extension of the associative `k`-algebra `R` by the
`R`-bimodule `M`, with the kernel explicitly identified with `M`. -/
structure SquareZeroExtension where
  /-- The extension algebra. -/
  E : Type z
  [ringE : Ring E]
  [algebraE : Algebra k E]
  /-- The quotient map `E → R`. -/
  projection : E →ₐ[k] R
  /-- The quotient map is surjective. -/
  projection_surjective : Function.Surjective projection
  /-- Identification of the kernel with the given bimodule. -/
  kernelEquiv : M ≃ₗ[k] LinearMap.ker projection.toLinearMap
  /-- The kernel has square zero. -/
  kernel_square_zero : ∀ m n : M,
    ((kernelEquiv m : LinearMap.ker projection.toLinearMap) : E) *
      ((kernelEquiv n : LinearMap.ker projection.toLinearMap) : E) = 0
  /-- Multiplication by a lift induces the prescribed left `R`-action on `M`. -/
  left_action : ∀ (e : E) (m : M),
    e * ((kernelEquiv m : LinearMap.ker projection.toLinearMap) : E) =
      ((kernelEquiv (projection e • m) : LinearMap.ker projection.toLinearMap) : E)
  /-- Multiplication by a lift induces the prescribed right `R`-action on `M`. -/
  right_action : ∀ (e : E) (m : M),
    ((kernelEquiv m : LinearMap.ker projection.toLinearMap) : E) * e =
      ((kernelEquiv ((MulOpposite.op (projection e) : Rᵐᵒᵖ) • m : M) :
        LinearMap.ker projection.toLinearMap) : E)

namespace SquareZeroExtension

attribute [instance] ringE algebraE

/-- A Hochschild splitting of a square-zero extension: a `k`-linear section
of the quotient map. -/
structure Splitting (S : SquareZeroExtension k R M) where
  /-- The chosen `k`-linear section `R → E`. -/
  splittingMap : R →ₗ[k] S.E
  /-- It is a right inverse to the quotient map. -/
  right_inv : S.projection.toLinearMap.comp splittingMap = LinearMap.id

/-- A square-zero extension is Hochschild when its underlying sequence is
split as a sequence of `k`-modules. -/
def IsHochschild (S : SquareZeroExtension k R M) : Prop :=
  Nonempty (Splitting k R M S)

/-- A factor set attached to a chosen splitting. The displayed equation is
exactly `f(r,s)=σ(r)σ(s)-σ(rs)`, transported through the kernel identification.

The Hochschild two-cocycle identity for this map is not part of the definition. -/
structure FactorSet (S : SquareZeroExtension k R M) (σ : Splitting k R M S) where
  /-- The `k`-bilinear factor set. -/
  map : R →ₗ[k] R →ₗ[k] M
  /-- The factor-set formula in the extension algebra. -/
  formula : ∀ r s : R,
    ((S.kernelEquiv (map r s) : LinearMap.ker S.projection.toLinearMap) : S.E) =
      σ.splittingMap r * σ.splittingMap s - σ.splittingMap (r * s)

/-- Equivalence of square-zero extensions over `R` and under the identified
kernel `M`. -/
structure Equiv (S T : SquareZeroExtension k R M) where
  /-- Algebra equivalence of the middle terms. -/
  algebraEquiv : S.E ≃ₐ[k] T.E
  /-- Compatibility with the quotient maps. -/
  over_base : T.projection.comp algebraEquiv.toAlgHom = S.projection
  /-- Compatibility with the fixed identifications of the kernel with `M`. -/
  on_kernel : ∀ m : M,
    algebraEquiv ((S.kernelEquiv m : LinearMap.ker S.projection.toLinearMap) : S.E) =
      ((T.kernelEquiv m : LinearMap.ker T.projection.toLinearMap) : T.E)

end SquareZeroExtension

end LeanCategories.Homological
