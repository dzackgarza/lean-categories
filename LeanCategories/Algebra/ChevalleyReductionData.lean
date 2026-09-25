/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Reduction of integral modules and Lie lattices

Definition-level realization of Humphreys FC14-C07-U040.

Given an admissible integral lattice `M`, its stabilizer lattice `L_V`, and
the integral Chevalley lattice `L(Z)`, Humphreys forms

* `V(K) = K ⊗[ℤ] M`,
* `L_V(K) = K ⊗[ℤ] L_V`, and
* `L(K) = K ⊗[ℤ] L(Z)`.

The inclusion `L(Z) ⊆ L_V` and the integral action on `M` then base-change
to the displayed maps over `K`.  The preceding source units prove that the
needed integral restrictions exist.  Sweep III therefore records the exact
graphs of those restrictions and of their scalar extensions; it does not
prove their totality, injectivity, Lie compatibility, or kernel statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

open TensorProduct

universe u v w x

/-- Humphreys' reduced module `V(K)=K⊗_ℤ M`. -/
abbrev reducedModuleData
    (K : Type u) (M : Type v)
    [CommRing K] [AddCommGroup M] [Module ℤ M] :=
  K ⊗[ℤ] M

/-- Scalar extension of an integral Lie lattice; used both for `L(K)` and
for `L_V(K)`. -/
abbrev reducedLieLatticeData
    (K : Type u) (LZ : Type v)
    [CommRing K] [AddCommGroup LZ] [Module ℤ LZ] :=
  K ⊗[ℤ] LZ

/-- Exact graph of the integral inclusion `L(Z) ⊆ L_V` when both lattices
are presented as submodules of the same ambient additive group. -/
def IsIntegralLieInclusionData
    {L : Type u} [AddCommGroup L]
    (LZ LV : Submodule ℤ L) (i : LZ →ₗ[ℤ] LV) : Prop :=
  ∀ x : LZ, ((i x : LV) : L) = (x : L)

/-- Exact graph of the integral stabilizer action on the chosen lattice `M`.

The ambient action is supplied as a `ℤ`-linear map into endomorphisms; for a
Lie module this is the restriction of its canonical Lie action. -/
def IsIntegralRestrictedActionData
    {L : Type u} {V : Type v}
    [AddCommGroup L] [Module ℤ L]
    [AddCommGroup V] [Module ℤ V]
    (LV : Submodule ℤ L) (M : Submodule ℤ V)
    (rho : L →ₗ[ℤ] Module.End ℤ V)
    (rhoZ : LV →ₗ[ℤ] Module.End ℤ M) : Prop :=
  ∀ x : LV, ∀ m : M,
    ((rhoZ x m : M) : V) = rho (x : L) (m : V)

/-- Exact scalar-extension graph of an integral inclusion.  On pure tensors
it is the source map `k⊗x ↦ k⊗i(x)`. -/
def IsReducedLieInclusionData
    {K : Type u} {LZ : Type v} {LV : Type w}
    [CommRing K]
    [AddCommGroup LZ] [Module ℤ LZ]
    [AddCommGroup LV] [Module ℤ LV]
    (i : LZ →ₗ[ℤ] LV)
    (iK : reducedLieLatticeData K LZ →ₗ[K] reducedLieLatticeData K LV) : Prop :=
  ∀ (k : K) (x : LZ),
    iK (k ⊗ₜ[ℤ] x) = k ⊗ₜ[ℤ] i x

/-- Exact scalar-extension graph of the stabilizer action
`L_V(K) → gl(V(K))`. -/
def IsReducedStabilizerActionData
    {K : Type u} {LV : Type v} {M : Type w}
    [CommRing K]
    [AddCommGroup LV] [Module ℤ LV]
    [AddCommGroup M] [Module ℤ M]
    (rhoZ : LV →ₗ[ℤ] Module.End ℤ M)
    (rhoK : reducedLieLatticeData K LV →ₗ[K]
      Module.End K (reducedModuleData K M)) : Prop :=
  ∀ (k : K) (x : LV) (a : K) (m : M),
    rhoK (k ⊗ₜ[ℤ] x) (a ⊗ₜ[ℤ] m) =
      (k * a) ⊗ₜ[ℤ] rhoZ x m

/-- Exact graph of the induced reduced representation
`L(K) → gl(V(K))`, obtained by composing the integral inclusion with the
integral stabilizer action before scalar extension.

No injectivity condition is imposed: this intentionally permits the central
kernel that Humphreys notes can occur in small characteristic. -/
def IsReducedChevalleyRepresentationData
    {K : Type u} {LZ : Type v} {LV : Type w} {M : Type x}
    [CommRing K]
    [AddCommGroup LZ] [Module ℤ LZ]
    [AddCommGroup LV] [Module ℤ LV]
    [AddCommGroup M] [Module ℤ M]
    (i : LZ →ₗ[ℤ] LV)
    (rhoZ : LV →ₗ[ℤ] Module.End ℤ M)
    (rhoK : reducedLieLatticeData K LZ →ₗ[K]
      Module.End K (reducedModuleData K M)) : Prop :=
  ∀ (k : K) (x : LZ) (a : K) (m : M),
    rhoK (k ⊗ₜ[ℤ] x) (a ⊗ₜ[ℤ] m) =
      (k * a) ⊗ₜ[ℤ] rhoZ (i x) m

end LeanCategories.Algebra
