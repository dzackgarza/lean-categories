/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.CartierLineBundleData
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Effective Cartier divisor data

Definition-level realization of Hartshorne FC06-C02-U198.

An effective Cartier divisor is a Cartier divisor admitting local equations
that are regular functions.  Since those equations represent units of the
total quotient sheaf, the corresponding regular functions are the local
non-zero-divisor generators of the associated ideal sheaf.  That ideal sheaf
defines the associated closed subscheme through Mathlib's native
`Scheme.IdealSheafData.subscheme` construction.

Sweep III records these clauses as predicates and selects the ideal-sheaf
datum by its local principal-generator specification.  Compatibility of the
local generators, local principality, codimension statements, and the
bijection with locally principal closed subschemes are result-layer content
(FC06-C02-U199) and are not proved here.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

variable {X : Scheme.{u}}

/-- A local equation of a Cartier divisor is regular when it comes from a
regular section which is a non-zero-divisor in the section ring. -/
def IsRegularCartierLocalEquationData (D : CartierDivisorData X)
    (U : X.Opens) (a : X.sheaf.presheaf.obj (op U))
    (f : Additive (TotalQuotientUnitSectionsData X U)) : Prop :=
  IsCartierLocalEquationData X D U f ∧
    a ∈ nonZeroDivisors Γ(X, U) ∧
      (toTotalQuotientSheafData X).hom.app (op U) a =
        (↑(Additive.toMul f) :
          (totalQuotientRingSheafData X).presheaf.obj (op U))

/-- Hartshorne's effectiveness predicate for a Cartier divisor: every point
has a neighbourhood carrying a regular local equation. -/
def IsEffectiveCartierDivisorData (D : CartierDivisorData X) : Prop :=
  ∀ x : X,
    ∃ (U : X.Opens) (_hx : x ∈ U)
      (a : X.sheaf.presheaf.obj (op U))
      (f : Additive (TotalQuotientUnitSectionsData X U)),
      IsRegularCartierLocalEquationData D U a f

/-- Specification of the ideal sheaf associated to an effective Cartier
divisor: on an affine neighbourhood carrying a regular local equation `a`,
the ideal is the principal ideal `(a)`.

The predicate records the source's gluing target without proving that the
locally principal presentations agree on overlaps. -/
def IsAssociatedEffectiveCartierIdealData (D : CartierDivisorData X)
    (I : X.IdealSheafData) : Prop :=
  ∀ x : X,
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (_hx : x ∈ U)
      (a : X.sheaf.presheaf.obj (op U))
      (f : Additive (TotalQuotientUnitSectionsData X U)),
      IsRegularCartierLocalEquationData D U a f ∧
        I.ideal ⟨U, hU⟩ = Ideal.span {a}

/-- The ideal-sheaf datum associated to `D`, selected by its local
principal-generator specification.  For an effective Cartier divisor,
FC06-C02-U199 supplies the later existence/specification theorem. -/
def associatedEffectiveCartierIdealData (D : CartierDivisorData X) :
    X.IdealSheafData :=
  Classical.epsilon (IsAssociatedEffectiveCartierIdealData D)

/-- The closed subscheme associated to an effective Cartier divisor. -/
def associatedEffectiveCartierSubschemeData (D : CartierDivisorData X) : Scheme :=
  (associatedEffectiveCartierIdealData D).subscheme

/-- Graph form of the associated closed-subscheme construction, retaining the
ideal-sheaf specification propositionally. -/
def IsAssociatedEffectiveCartierSubschemeData (D : CartierDivisorData X)
    (Y : Scheme.{u}) : Prop :=
  ∃ I : X.IdealSheafData,
    IsAssociatedEffectiveCartierIdealData D I ∧ Y = I.subscheme

end LeanCategories.Schemes
