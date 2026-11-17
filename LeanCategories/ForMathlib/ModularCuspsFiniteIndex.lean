/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.GroupTheory.Index

/-!
# The cusps of a finite-index subgroup of `SL(2, ℤ)`

A cusp of a subgroup `𝒢 ≤ GL(2, ℝ)` is a fixed point of a parabolic element
(`IsCusp`), and `CuspOrbits 𝒢` is the set of `𝒢`-orbits of its cusps
(`Mathlib/NumberTheory/ModularForms/Cusps.lean`). Mathlib proves that an arithmetic subgroup has
finitely many cusp orbits, through a surjection from the finite coset space
`SL(2, ℤ) ⧸ (𝒢 ⊓ SL(2, ℤ))` onto `CuspOrbits 𝒢` (`cosetToCuspOrbit`,
`surjective_cosetToCuspOrbit`), and that a subgroup of `SL(2, ℤ)` is arithmetic exactly when it has
finite index (`isArithmetic_iff_finiteIndex`).

Search record (LC-09): `scripts/formalization_corpus.py search` at the manifest head `6d97e8ad`
under `cusps finite index subgroup modular group`. The Lean hit is
`Mathlib/NumberTheory/ModularForms/Cusps.lean` and `.../ArithmeticSubgroups.lean`, used below; the
non-Lean hit is Isabelle/AFP `thys/Elliptic_Functions/Modular_Subgroups.thy`, a reference
implementation with no transportable Lean content.

So the finiteness of the cusps of a finite-index subgroup of `SL(2, ℤ)` is Mathlib's arithmetic
instance, and the count is bounded by the index of the subgroup — through the same surjective coset
map, which is the coset-table half of a Todd–Coxeter computation
(`LeanCategories.ForMathlib.CosetTable`): a certified table on `k` points gives `Γ.index ≤ k`, and
then `Nat.card (CuspOrbits Γ) ≤ k` is the cusp count. The two statements here are the glue that
turns those Mathlib facts into that bound; no cusp is enumerated.
-/

@[expose] public section

namespace LeanCategories.ForMathlib

open Matrix SpecialLinearGroup GeneralLinearGroup

open scoped MatrixGroups

/-- **A finite-index subgroup of `SL(2, ℤ)` has finitely many cusps.** -/
theorem finite_cuspOrbits_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Finite (CuspOrbits Γ) :=
  inferInstance

/-- The subgroup of `SL(2, ℤ)` cut out by a subgroup of `GL(2, ℝ)` that contains it is itself. -/
theorem comap_mapGL_eq (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).comap (mapGL ℝ) = Γ := by
  ext x
  constructor
  · intro hx
    have hx' : (mapGL ℝ x : GL (Fin 2) ℝ) ∈ Subgroup.map (mapGL ℝ) Γ := hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : y = x := SpecialLinearGroup.mapGL_injective hyx
    simpa [hyx'] using hy
  · intro hx
    exact Subgroup.mem_map_of_mem _ hx

/-- **A finite-index subgroup of `SL(2, ℤ)` has at most its index of cusps**, through the surjection
from its coset space onto its cusp orbits. -/
theorem natCard_cuspOrbits_le_index (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Nat.card (CuspOrbits Γ) ≤ Γ.index := by
  have hsurj := surjective_cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ))
  refine (Nat.card_le_card_of_surjective _ hsurj).trans_eq ?_
  rw [comap_mapGL_eq, Subgroup.index_eq_card]

end LeanCategories.ForMathlib
