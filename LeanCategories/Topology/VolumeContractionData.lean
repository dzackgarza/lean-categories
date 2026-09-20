/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Volume-form contraction data

Definition-level realization of Lee FC08-C16-U040.

Lee's map `beta(X) = X ⨼ dV_g` is, fiberwise, ordinary interior
multiplication of a top alternating form by its first vector argument.
Mathlib's `AlternatingMap.curryLeft` is exactly this construction.

Sweep III records the fibre map and its pointwise action on a family of
fibres. It also records raw forward/inverse data for the source's named
bundle isomorphism, selected by the intrinsic requirement that the forward
map be contraction. The inverse identities and smoothness are result-layer
statements and are not proof fields of the data carrier.
-/

@[expose] public section

namespace LeanCategories.Topology

universe u v

/-- Interior multiplication by a top-degree alternating form, viewed as a
linear map from vectors to one-lower-degree alternating forms. -/
def volumeContractionAt {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (vol : V [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) :
    V →ₗ[ℝ] V [⋀^Fin n]→ₗ[ℝ] ℝ :=
  vol.curryLeft

/-- Pointwise volume contraction on a family of vector spaces.

For a tangent-space family and the Riemannian volume form `dV_g`, this is
Lee's defining formula `beta(X)_p = i_{X_p}(dV_g)_p`. -/
def volumeContractionFieldData
    {B : Type v} {E : B → Type u}
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    {n : ℕ} (vol : ∀ b, E b [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ)
    (X : ∀ b, E b) : ∀ b, E b [⋀^Fin n]→ₗ[ℝ] ℝ :=
  fun b => volumeContractionAt (vol b) (X b)

/-- Raw forward/inverse data for the fibre isomorphism induced by a
top-degree continuous alternating form.

No inverse-law proof is stored in this carrier. This is intentional: Lee's
claim that contraction by a volume form is an isomorphism is the result that
certifies these two maps as mutual inverses. -/
structure VolumeContractionEquivData
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) where
  forward : V →L[ℝ] V [⋀^Fin n]→L[ℝ] ℝ
  inverse : (V [⋀^Fin n]→L[ℝ] ℝ) →L[ℝ] V

noncomputable instance {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ} :
    Inhabited (VolumeContractionEquivData V n) :=
  ⟨⟨0, 0⟩⟩

/-- Intrinsic specification of the volume-contraction isomorphism data.

The forward map must be `v ↦ i_v vol`; the two remaining clauses are exactly
the inverse identities that the later isomorphism theorem proves. -/
def IsVolumeContractionEquivData
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (vol : V [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (D : VolumeContractionEquivData V n) : Prop :=
  D.forward = vol.curryLeft ∧
    (∀ v, D.inverse (D.forward v) = v) ∧
      ∀ ω, D.forward (D.inverse ω) = ω

/-- Lee's fibrewise isomorphism data, selected from the contraction
characterization without requiring inverse proofs from a caller. -/
noncomputable def volumeContractionEquivData
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (vol : V [⋀^Fin (n + 1)]→L[ℝ] ℝ) :
    VolumeContractionEquivData V n :=
  Classical.epsilon (IsVolumeContractionEquivData vol)

/-- A pointwise family of raw volume-contraction isomorphism data. For a
Riemannian volume form on tangent fibres this is the definition-level carrier
underlying Lee's smooth bundle isomorphism `β`.

Smoothness of the forward/inverse total-space maps is a separate result and
is deliberately not stored here. -/
abbrev VolumeContractionBundleIsoData
    {B : Type v} (E : B → Type u)
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)] (n : ℕ) :=
  ∀ b, VolumeContractionEquivData (E b) n

/-- The selected pointwise bundle-isomorphism data for a family of top forms. -/
noncomputable def volumeContractionBundleIsoData
    {B : Type v} {E : B → Type u}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)] {n : ℕ}
    (vol : ∀ b, E b [⋀^Fin (n + 1)]→L[ℝ] ℝ) :
    VolumeContractionBundleIsoData E n :=
  fun b => volumeContractionEquivData (vol b)

end LeanCategories.Topology
