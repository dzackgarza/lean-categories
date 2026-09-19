/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Quotient carrier data for CW pairs

Hatcher, *Algebraic Topology*, Chapter 0 (FC07-C00-U018).

This file records only the quotient that collapses the chosen subcomplex to
one class. Cell inheritance, attaching maps, and the CW axioms are result-layer
material for the Definitions/Theorems phase boundary.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

inductive CWQuotientClass (X : Type u) where
  | collapsed
  | point (x : X)

/-- Classifier that sends the collapsed subspace to one class and keeps every
point outside it distinct. -/
noncomputable def cwQuotientClassify {X : Type u} (A : Set X) (x : X) :
    CWQuotientClass X := by
  classical
  exact if x ∈ A then .collapsed else .point x

/-- The quotient relation for collapsing `A` to one point. -/
noncomputable def cwQuotientSetoid {X : Type u} (A : Set X) : Setoid X :=
  Setoid.ker (cwQuotientClassify A)

/-- The carrier of the quotient `X/A`. -/
abbrev CWQuotient {X : Type u} (A : Set X) : Type u :=
  Quotient (cwQuotientSetoid A)

/-- The canonical quotient map `X → X/A`. -/
noncomputable def cwQuotientMk {X : Type u} (A : Set X) : X → CWQuotient A :=
  Quotient.mk _

end LeanCategories.Topology
