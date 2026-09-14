/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Grade and Cohen--Macaulay local rings

Weibel, *An Introduction to Homological Algebra*, More Definitions 4.4.3
(FC05-C04-U050).

For a finitely generated module over a commutative Noetherian local ring, Weibel defines
the grade as the maximal length of a module-regular sequence contained in the maximal ideal,
and calls the ring Cohen--Macaulay when the grade of its regular module equals its Krull
dimension.

Mathlib already owns regular sequences in `RingTheory.Sequence.IsRegular` and the Rees theorem
relating regular sequences to Ext-vanishing in `Mathlib.RingTheory.Depth.Rees`.  The missing
grade/Cohen--Macaulay vocabulary is adapted from mathlib4 PR #26218, commit
`2a84ea75981e352045999fd11bc7ef6b8fab549f` (`RingTheory/Depth/Basic.lean` and
`RingTheory/CohenMacaulay/Basic.lean`).  Unlike that reference branch, this file keeps Weibel's
regular-sequence definition of grade primitive; the Ext characterization is a theorem, not part
of Definition 4.4.3.
-/

@[expose] public section

open RingTheory.Sequence

universe v u

variable {R : Type u} [CommRing R]

namespace IsLocalRing

/-- A grade sequence for `M` is an `M`-regular sequence all of whose entries lie in the maximal
ideal.  This is exactly the class of sequences over which Weibel takes the maximal length in
Definition 4.4.3. -/
def IsGradeSequence [IsLocalRing R] (M : ModuleCat.{v} R) (rs : List R) : Prop :=
  IsRegular M rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal R

/-- The grade of a module over a local ring, as the supremum of lengths of regular sequences in
the maximal ideal.  Under Weibel's Noetherian finite-module hypotheses this is the usual finite
maximal length; `ℕ∞` lets the definition itself avoid baking the boundedness theorem into the
data. -/
noncomputable def grade [IsLocalRing R] (M : ModuleCat.{v} R) : ℕ∞ :=
  sSup {(rs.length : ℕ∞) | (rs : List R) (_ : IsGradeSequence M rs)}

/-- The empty sequence is a grade sequence on every nonzero module. -/
theorem isGradeSequence_nil [IsLocalRing R] (M : ModuleCat.{v} R) [Nontrivial M] :
    IsGradeSequence M [] := by
  refine ⟨IsRegular.nil R M, ?_⟩
  simp

/-- Membership in the maximal ideal is genuine defining data: the singleton sequence `[1]`
is never a grade sequence. -/
theorem not_isGradeSequence_one [IsLocalRing R] (M : ModuleCat.{v} R) :
    ¬ IsGradeSequence M [1] := by
  intro h
  have h1 : (1 : R) ∈ maximalIdeal R := h.2 1 (by simp)
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end IsLocalRing

/-- In Weibel §4.4, a local ring is by convention commutative Noetherian local.  Such a ring is
Cohen--Macaulay when the grade of the regular module equals its Krull dimension (Definition
4.4.3). -/
class IsCohenMacaulayLocalRing (R : Type u) [CommRing R] : Prop
    extends IsLocalRing R where
  /-- The standing §4.4 convention includes Noetherianity.  This is an instance field so
  downstream source units recover the convention directly from Cohen--Macaulayness. -/
  isNoetherianRing : IsNoetherianRing R
  grade_eq_dim : ringKrullDim R = IsLocalRing.grade (ModuleCat.of R R)

attribute [instance] IsCohenMacaulayLocalRing.isNoetherianRing

theorem isCohenMacaulayLocalRing_def (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    IsCohenMacaulayLocalRing R ↔
      ringKrullDim R = IsLocalRing.grade (ModuleCat.of R R) :=
  ⟨fun h => h.grade_eq_dim, fun h => ⟨inferInstance, h⟩⟩
