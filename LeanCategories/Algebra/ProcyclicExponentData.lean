/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.ProfiniteIntegerData
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Procyclic exponent notation

Definition-level realization of Serre FC10-C13-U007.

For an element `s` of a profinite group, the ordinary homomorphism from
`Multiplicative ℤ` sending the additive generator `1` to `s` is
`zpowersHom _ s`. Since Serre's `Z-hat` is represented locally by the
profinite completion of `Multiplicative ℤ`, Mathlib's native profinite
completion lift extends this homomorphism canonically and continuously.

The value of that extension at `ν ∈ Z-hat` is the source notation `s^ν`.
The universal-property equations and uniqueness of the lift are already owned
by `ProfiniteGrp.ProfiniteCompletion.lift_eta` and `lift_unique`; no new
result-layer theorem is added here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

open CategoryTheory

variable {P : ProfiniteGrp}

/-- The cyclic homomorphism `ℤ → P` whose additive generator maps to `s`,
written on `Multiplicative ℤ` to match the local profinite-completion carrier. -/
def serreProcyclicIntegerHomData (s : P) :
    GrpCat.of (Multiplicative ℤ) ⟶ GrpCat.of P :=
  GrpCat.ofHom (zpowersHom P s)

/-- Serre's canonical continuous map `f_s : Z-hat → P`. -/
def serreProcyclicExponentMapData (s : P) :
    serreProfiniteIntegerData ⟶ P :=
  ProfiniteGrp.ProfiniteCompletion.lift (serreProcyclicIntegerHomData s)

/-- Serre's continuous exponent notation `s^ν := f_s(ν)`. -/
def serreProcyclicExponentData (s : P)
    (ν : serreProfiniteIntegerData) : P :=
  serreProcyclicExponentMapData s ν

end LeanCategories.Algebra
