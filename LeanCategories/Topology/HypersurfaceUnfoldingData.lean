/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.MilnorFiberData
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A hypersurface unfolding and its discriminant

Definition data for Peters--Sterk FC11-C18-U030, Version JUNE 2024,
printed p. 334, Section 18.2.B, equation (18.3).

For the source's chosen monomial exponents, the family is
`F(z,u) = f(z) + u₀ + ∑ j, uⱼ z^(Bⱼ)`. The parameter count below is
`m + 1`: the constant parameter is separated from the other `m` parameters.
The source chooses the monomials together with `1` to represent a basis
of its Tjurina algebra. That choice, analyticity, and semiuniversality are
not asserted for arbitrary inputs to these raw formulas.

The total family is the actual zero locus of `F`, and its map to the base
is the parameter projection. Its discriminant consists of parameters of
singular fibres: there is a point in the chosen neighbourhood where both
`F` and its differential in the **z variables** vanish. `HasFDerivAt`
records a genuine zero differential; it does not mistake the default zero
value of `fderiv` at a nondifferentiable point for a critical point.

The printed display `(z,u₀,u) ↦ (F(z,u₀,u),u)` cannot literally be used
for this purpose: varying `u₀` supplies the first target direction, so it
has no critical points when the family is holomorphic. The definitions
here retain the preceding zero-hypersurface family and its base parameters,
rather than silently assigning the discriminant to that ambient map.

All defining subsets and functions use native finite products/sums,
Euclidean coordinates, the Fréchet-derivative predicate, subtypes and set
images. No analytic-germ theory, deformation functor, Jacobian quotient,
generic quotient framework, or supplied discriminant is introduced.
Hypersurface, semiuniversality, local-triviality and monodromy statements
remain result content. This module contains no supporting proofs.
-/

@[expose] public section

open scoped BigOperators

namespace LeanCategories.Topology

/-- The constant unfolding parameter and the remaining `m` parameters. -/
abbrev HypersurfaceUnfoldingParameterData (m : ℕ) := ℂ × (Fin m → ℂ)

/-- Equation (18.3), using the source's chosen nonconstant monomials.
The constant monomial has its own parameter, so it is not summed twice. -/
def hypersurfaceUnfoldingFunctionData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (u : HypersurfaceUnfoldingParameterData m)
    (z : MilnorCoordinateSpaceData n) : ℂ :=
  f z + u.1 + ∑ j, u.2 j * ∏ i, z i ^ B j i

/-- The actual zero-hypersurface family, restricted to the chosen source
neighbourhood `V` and parameter neighbourhood `U`. Openness and sufficiently
small size are source specializations, not supplied construction proofs. -/
def hypersurfaceUnfoldingTotalSpaceSetData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) :
    Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m) :=
  {p | p ∈ V ∧ p.2 ∈ U ∧ hypersurfaceUnfoldingFunctionData f B p.2 p.1 = 0}

/-- The zero-locus carrier with the native subspace topology. -/
abbrev HypersurfaceUnfoldingTotalSpaceData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) : Type :=
  hypersurfaceUnfoldingTotalSpaceSetData f B V U

/-- Parameter projection of the constructed family. Membership in the
chosen base is already part of a point of its total space. -/
def hypersurfaceUnfoldingProjectionData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) :
    HypersurfaceUnfoldingTotalSpaceData f B V U → U :=
  fun p ↦ ⟨p.1.2, p.2.2.1⟩

/-- Points of the total family at which the fibre's defining function has
zero complex differential. The parameters are held fixed. -/
def hypersurfaceUnfoldingCriticalSetData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) :
    Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m) :=
  {p | p ∈ hypersurfaceUnfoldingTotalSpaceSetData f B V U ∧
    HasFDerivAt (hypersurfaceUnfoldingFunctionData f B p.2)
      (0 : MilnorCoordinateSpaceData n →L[ℂ] ℂ) p.1}

/-- The discriminant in the parameter space: the image of the actual
fibre-critical locus, not a polynomial discriminant or a supplied set. -/
def hypersurfaceUnfoldingDiscriminantData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) :
    Set (HypersurfaceUnfoldingParameterData m) :=
  Prod.snd '' hypersurfaceUnfoldingCriticalSetData f B V U

end LeanCategories.Topology
