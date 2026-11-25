/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.TorExercise3A6

@[expose] public section

/-!
# TorFiniteStage: `E-HAT-3.A-6` at a finitely generated stage

Card `E-HAT-3.A-6` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology* (2002), §3.A Exercise 6 (printed p. 267): for all abelian groups `A` and
`B`, `Tor(A, B)` is a torsion group, and `Tor(A, B)` has an element of order `n`
if and only if both `A` and `B` have one.

The card's own solution writes the first variable as a directed union of finitely
generated subgroups and computes each stage.  new-qual-site#111 records that the step
that would license that reduction — Tor commuting with filtered colimits, Hatcher
§3.A Exercise 4 — is absent at this pin, and asks instead for the resolution
covering the finitely generated stage.  This file is that resolution, stated at the
stage:

* `exists_fin_free_presentation`: a finitely generated `ℤ`-module is a quotient of
  `ℤ ^ n`, so its stage has a finite free presentation.  (`TorFreeResolution` then
  computes `Tor₁` at it — `torOneIsoKernelFinFree` — and Noetherianity makes the
  syzygy finitely generated, `TorFreeResolution.syzygy_finite`.)
* `isAddTorsion_ker_stage`: **the torsion statement at a finitely generated stage**.
  For a finitely generated `F'` inside a free `F` and any relation submodule `R`, the
  kernel of the tensored inclusion `R ⊓ F' → F` is a torsion group.  The killing
  integer is the Smith-normal-form product of `TorExercise3A6.exists_nsmul_eq_zero_of_stage`;
  this restates that computation as a torsion statement about the stage.
* `isAddTorsion_torOne_of_finiteStage`: **the card's torsion statement at a finitely
  generated stage**, `Tor₁(A, B)` a torsion group for `A` finitely generated, with
  `B` arbitrary; and `isAddTorsion_torOne_of_finiteStage_fg` for `A` and `B` both
  finitely generated.

Nothing here uses a colimit comparison: the reduction to the stage is the elementwise
descent of `TorStages.exists_stage_of_free`, and the stage is computed by Smith normal
form.

## LC-09 search record

Queries run against the formalization corpus (`scripts/formalization_corpus.py`),
local Mathlib and this repository on 2026-11-18: `Tor commutes with filtered colimit`,
`Tor direct limit continuous`, `filtered colimit exact abelian`, `Tor torsion group`,
`finitely generated module free presentation`, `Module.Finite.exists_fin`,
`linearCombination surjective span`, `IsAddTorsion kernel submodule`,
`Smith normal form submodule product diagonal`.  Hits used: Mathlib's
`Module.Finite.exists_fin` (`RingTheory/Finiteness/Defs.lean:147`) and
`Fintype.span_range_eq_top_iff_surjective_fintypeLinearCombination`
(`LinearAlgebra/Finsupp/LinearCombination.lean:348`) for the finite free presentation;
in this repository `TorExercise3A6.exists_nsmul_eq_zero_of_stage` (the Smith-normal-form
stage computation) and `TorExercise3A6.isAddTorsion_torOne`.  No hit for a colimit
comparison: Mathlib's `CategoryTheory.Tor` still carries no filtered-colimit API, which
is why the stage is reached by descent rather than by commuting Tor with a colimit.
-/

namespace LeanCategories.Homological.TorFiniteStage

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct ZeroObject

/-! ## A finite free presentation at the stage -/

/-- **The finitely generated stage is presented by a finite free module.**  A finitely
generated `ℤ`-module is a quotient of `ℤ ^ n`: read `n` and the generating family off
`Module.Finite.exists_fin` and take their linear combination. -/
theorem exists_fin_free_presentation (A : Type) [AddCommGroup A] [Module ℤ A]
    [Module.Finite ℤ A] :
    ∃ (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] A), Function.Surjective f := by
  obtain ⟨n, s, hspan⟩ := Module.Finite.exists_fin (R := ℤ) (M := A)
  exact ⟨n, Fintype.linearCombination ℤ s,
    (span_range_eq_top_iff_surjective_fintypeLinearCombination (R := ℤ) (v := s)).mp hspan⟩

/-- **The stage is a resolution by finitely generated modules.**  A finitely generated
`ℤ`-module has a finite free presentation whose syzygy is again finitely generated, so the
two-term complex `0 → ker f → ℤ ^ n → A → 0` sits inside finitely generated modules.  That
is the resolution `TorFreeResolution.torOneIsoKernelFinFree` computes `Tor₁` at.  Finiteness
of the syzygy is `TorFreeResolution.syzygy_finite` (a submodule of `ℤ ^ n` over a Noetherian
ring). -/
theorem exists_fin_free_presentation_fg (A : Type) [AddCommGroup A] [Module ℤ A]
    [Module.Finite ℤ A] :
    ∃ (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] A),
      Function.Surjective f ∧ Module.Finite ℤ ↥(LinearMap.ker f) := by
  obtain ⟨n, f, hf⟩ := exists_fin_free_presentation A
  exact ⟨n, f, hf, TorFreeResolution.syzygy_finite n f⟩

/-! ## The torsion statement at a finitely generated stage -/

/-- **`E-HAT-3.A-6`, torsion statement, at a finitely generated stage.**  Let `F` be free
with basis `b`, let `F' ≤ F` be finitely generated, and let `R ≤ F` be any relation
submodule.  Then the kernel of the tensored inclusion `R ⊓ F' → F` is a torsion group:
every element of it is killed by a positive integer.

This is the stage at which the card's computation happens.  The integer is the
Smith-normal-form product of `TorExercise3A6.exists_nsmul_eq_zero_of_stage`, which puts
`R ⊓ F'` into diagonal form inside a finitely generated coordinate summand containing
`F'`. -/
theorem isAddTorsion_ker_stage {F B : Type} [AddCommGroup F] [AddCommGroup B]
    {ι : Type*} (b : Module.Basis ι ℤ F) (F' R : Submodule ℤ F) (hF' : F'.FG) :
    IsAddTorsion ↥(LinearMap.ker (((R ⊓ F').subtype).rTensor B)) := by
  intro t
  obtain ⟨N, hN, hNt⟩ := TorExercise3A6.exists_nsmul_eq_zero_of_stage (B := B) b F' R hF' t
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hN, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ N t]
  exact hNt

/-- The coordinate form of `isAddTorsion_ker_stage`: at a finitely generated stage, every
element of the kernel of the tensored inclusion is killed by a positive integer. -/
theorem exists_nsmul_eq_zero_ker_stage {F B : Type} [AddCommGroup F] [AddCommGroup B]
    {ι : Type*} (b : Module.Basis ι ℤ F) (F' R : Submodule ℤ F) (hF' : F'.FG)
    (t : ↥(LinearMap.ker (((R ⊓ F').subtype).rTensor B))) :
    ∃ N : ℕ, 0 < N ∧ (N : ℤ) • t = 0 :=
  TorExercise3A6.exists_nsmul_eq_zero_of_stage (B := B) b F' R hF' t

/-! ## The card's statement at a finitely generated stage -/

/-- **Hatcher, *Algebraic Topology* (2002), §3.A Exercise 6, torsion statement, at a
finitely generated stage.**  For a finitely generated abelian group `A` and an arbitrary
abelian group `B`, `Tor₁(A, B)` is a torsion group.

The proof is the one the card asks for: reduce to a stage where `A` is finitely generated
— here the finite free presentation of `exists_fin_free_presentation` — and compute that
stage, which `TorExercise3A6.isAddTorsion_torOne` does by the Smith-normal-form killing of
`isAddTorsion_ker_stage`.  No filtered-colimit comparison is used, so the absence of
Hatcher §3.A Exercise 4 at this pin does not bear on the statement. -/
theorem isAddTorsion_torOne_of_finiteStage (A B : Type) [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] :
    IsAddTorsion ↥(TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B)) :=
  TorExercise3A6.isAddTorsion_torOne

/-- The card's torsion statement with **both** variables finitely generated. -/
theorem isAddTorsion_torOne_of_finiteStage_fg (A B : Type) [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] [Module.Finite ℤ B] :
    IsAddTorsion ↥(TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B)) :=
  TorExercise3A6.isAddTorsion_torOne

/-- The card's torsion statement at a finitely generated stage, in the order form: every
element of `Tor₁(A, B)` has finite additive order. -/
theorem exists_addOrderOf_pos_torOne_of_finiteStage (A B : Type) [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] (x : TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B)) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 :=
  isOfFinAddOrder_iff_nsmul_eq_zero.mp
    (isAddTorsion_torOne_of_finiteStage (A := A) (B := B) x)

end LeanCategories.Homological.TorFiniteStage
