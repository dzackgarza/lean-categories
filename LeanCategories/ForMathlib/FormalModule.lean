/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic

@[expose] public section

/-!
# Formal modules

This file records Neukirch's definition of a formal `O`-module from *Algebraic Number
Theory*, Chapter V, Section 4, Definition 4.4 (FC09-C05-U039). The definition is expanded into
power-series equations: the bracket series are formal-group endomorphisms, preserve zero, one,
addition and multiplication, and have linear coefficient `a`.

The formal-group-homomorphism field follows the proof-complete reference interface
`FormalGroupHom` in leanprover-community/mathlib4 PR #38213 at commit
`133714768d42ba1a6107b7a84e2d22222c7c69ed` (Apache-2.0). The ring operations are stated
directly here because the pinned Mathlib does not yet bundle the endomorphism ring.
-/

noncomputable section

open MvPowerSeries

namespace LeanCategories

variable {O : Type*} [CommRing O]

/-- A power series which is an endomorphism of the formal group `F`. -/
structure IsFormalGroupEndomorphism (F : FormalGroup O) (f : PowerSeries O) : Prop where
  /-- A formal-group endomorphism has zero constant coefficient. -/
  zero_constantCoeff : f.constantCoeff = 0
  /-- The equation `f(F(X,Y)) = F(f(X),f(Y))`. -/
  map_formalGroup : f.subst F.toPowerSeries =
    F.toPowerSeries.subst (f.toMvPowerSeries ·)

/-- A formal `O`-module: a formal group over `O` together with the scalar endomorphisms
`[a]_F(X)`, written as the equations expressing the ring homomorphism
`O → End_O(F)` and the congruence `[a]_F(X) ≡ aX mod deg 2`. -/
structure FormalModule (O : Type*) [CommRing O] where
  /-- The underlying one-dimensional formal group law. -/
  formalGroup : FormalGroup O
  /-- Neukirch's standing formal-group definition includes commutativity. -/
  formalGroup_comm : formalGroup.IsComm
  /-- The scalar endomorphism `[a]_F(X)`. -/
  bracket : O → PowerSeries O
  /-- Every bracket series is an endomorphism of the underlying formal group. -/
  bracket_endomorphism : ∀ a, IsFormalGroupEndomorphism formalGroup (bracket a)
  /-- The scalar zero acts by the zero series. -/
  bracket_zero : bracket 0 = 0
  /-- The scalar one acts by the identity series. -/
  bracket_one : bracket 1 = PowerSeries.X
  /-- Addition in `O` is formal-group addition of the bracket series. -/
  bracket_add : ∀ a b, bracket (a + b) =
    formalGroup.toPowerSeries.subst ![bracket a, bracket b]
  /-- Multiplication in `O` is composition of the bracket series. -/
  bracket_mul : ∀ a b, bracket (a * b) = (bracket a).subst (bracket b)
  /-- The linear coefficient of `[a]_F(X)` is `a`. -/
  bracket_coeff_one : ∀ a, (bracket a).coeff 1 = a

end LeanCategories
