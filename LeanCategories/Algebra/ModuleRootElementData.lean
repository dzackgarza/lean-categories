/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.ChevalleyReductionData
public import LeanCategories.Algebra.KostantAdmissibleLatticeData
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Root elements on reduced modules

Definition-level realization of Humphreys FC14-C07-U041.

For an admissible integral lattice `M`, the divided powers of a chosen root
vector preserve `M`.  After scalar extension to a coefficient ring `K`, their
finite polynomial sum

`x_α(c) = Σ_t c^t x_{α,t}`

is the source root element on `V(K)=K⊗[ℤ]M`.

The local definitions use exact graphs.  Existence of the integral divided-
power restrictions, eventual vanishing, invertibility of the polynomial sum,
and determinant one are result obligations; none is proved in Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

open TensorProduct
open scoped BigOperators

universe u v w x y

/-- Exact graph of the `n`-th divided power of a root vector restricted to an
integral lattice `M`. -/
def IsIntegralModuleDividedPowerData
    {F : Type u} {L : Type v} {V : Type w} {Phi : Type x}
    [Field F] [CharZero F] [LieRing L] [LieAlgebra F L]
    [AddCommGroup V] [Module F V] [LieRingModule L V] [LieModule F L V]
    (rootVector : Phi → L) (M : Submodule ℤ V)
    (alpha : Phi) (n : ℕ) (d : Module.End ℤ M) : Prop :=
  ∀ m : M,
    ((d m : M) : V) =
      kostantUEARepresentation F L V
        (ueaDividedPower F L (rootVector alpha) n) (m : V)

/-- Exact graph of scalar-extending an integral divided-power endomorphism to
`V(K)`. -/
def IsReducedModuleDividedPowerData
    {K : Type u} {M : Type v}
    [CommRing K] [AddCommGroup M] [Module ℤ M]
    (d : Module.End ℤ M)
    (dK : Module.End K (reducedModuleData K M)) : Prop :=
  ∀ (a : K) (m : M),
    dK (a ⊗ₜ[ℤ] m) = a ⊗ₜ[ℤ] d m

/-- Exact graph of Humphreys' polynomial root element
`x_α(c)=Σ_t c^t x_{α,t}` as a candidate element of `GL(V(K))`.

The existential family `d` is pinned term-by-term to the canonical divided-
power action above.  Its eventual vanishing is part of the graph, so the
displayed sum is genuinely finite without choosing an arbitrary truncation.
Existence of such a family and of the `GL` lift is deferred. -/
def IsModuleRootElementData
    {F : Type u} {L : Type v} {V : Type w} {Phi : Type x} {K : Type y}
    [Field F] [CharZero F] [LieRing L] [LieAlgebra F L]
    [AddCommGroup V] [Module F V] [LieRingModule L V] [LieModule F L V]
    [CommRing K]
    (rootVector : Phi → L) (M : Submodule ℤ V)
    (alpha : Phi) (c : K)
    (g : LinearMap.GeneralLinearGroup K (reducedModuleData K M)) : Prop :=
  ∃ d : ℕ → Module.End ℤ M,
    (∀ n : ℕ, IsIntegralModuleDividedPowerData
      (F := F) (L := L) (V := V) (Phi := Phi) rootVector M alpha n (d n)) ∧
    ∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → d n = 0) ∧
      ∀ (a : K) (m : M),
        g.val (a ⊗ₜ[ℤ] m) =
          ∑ n ∈ Finset.range N, (c ^ n * a) ⊗ₜ[ℤ] d n m

end LeanCategories.Algebra
