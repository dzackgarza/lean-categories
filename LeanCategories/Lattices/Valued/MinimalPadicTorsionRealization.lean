/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DeterminantLine
public import LeanCategories.Lattices.Valued.Discriminant
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The minimal-rank p-adic lattice associated to a torsion form

Peters--Sterk use `L_{b#}` for the uniquely determined p-adic lattice of rank equal to the
length of a nondegenerate symmetric p-primary torsion form `b#` and having discriminant form
`b#` (`FC11-C11-U005`).

Here the length is the minimum number of generators of the underlying p-adic module. Valid
realization data are lattices carrying the source realization predicate. Proposition 11.1.3 is
the separate existence and uniqueness result; no arbitrary lattice is selected beforehand.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The rank-zero p-adic lattice, used only to witness that the ambient lattice category is
nonempty before making the source's classical choice. -/
def padicRankZeroFiniteLattice (p : ℕ) [Fact p.Prime] :
    FiniteProjectiveLatticeCat ℤ_[p] ℤ_[p] := by
  let A : Matrix (Fin 0) (Fin 0) ℤ_[p] := 0
  have hA : A.IsSymm := Matrix.IsSymm.ext fun i ↦ Fin.elim0 i
  refine ⟨⟨BilinModuleCat.ofBilinMap (Matrix.toBilin' A), ?_, ?_⟩, ?_⟩
  · change Module.Projective ℤ_[p] (Fin 0 → ℤ_[p])
    infer_instance
  · intro x y
    exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA).eq x y
  · change Module.Finite ℤ_[p] (Fin 0 → ℤ_[p])
    infer_instance

/-- The minimum number of p-adic module generators of a finite p-adic module. -/
def padicModuleLength (p : ℕ) [Fact p.Prime] (M : Type*) [AddCommGroup M] [Module ℤ_[p] M] : ℕ :=
  (⊤ : Submodule ℤ_[p] M).spanFinrank

/-- A p-adic lattice has the source specification for `L_{b#}` when its rank is the length of
`b#`, its rationalized form is perfect, and its discriminant form is isometric to `b#`. -/
def RealizesMinimalPadicTorsionForm
    (p : ℕ) [Fact p.Prime] (_hpOdd : p ≠ 2)
    (q : NonsingularFiniteTorsionBilinModuleCat ℤ_[p] (FractionValueQuotient ℤ_[p]))
    (L : FiniteProjectiveLatticeCat ℤ_[p] ℤ_[p]) : Prop := by
  letI : Module.Finite ℤ_[p] L.obj.obj.carrier := L.property
  let qFinite : FiniteFormCat ℤ_[p] (FractionValueQuotient ℤ_[p]) :=
    ⟨q.obj, ⟨q.property.1, q.property.2.2.1⟩⟩
  exact ∃ hL : IsFractionFieldPerfect ℤ_[p] L.obj,
    L.genericRank = padicModuleLength p q.obj.carrier ∧
      Nonempty (discriminantFormModule ℤ_[p] L.obj hL ≅ qFinite)

/-- Source-faithful Peters--Sterk realization data for `L_{b#}`: a p-adic
lattice together with the exact minimal-rank/discriminant-form specification.
Proposition 11.1.3 supplies existence and uniqueness later. -/
abbrev MinimalPadicTorsionRealizationData
    (p : ℕ) [Fact p.Prime] (hpOdd : p ≠ 2)
    (q : NonsingularFiniteTorsionBilinModuleCat ℤ_[p] (FractionValueQuotient ℤ_[p])) :=
  {L : FiniteProjectiveLatticeCat ℤ_[p] ℤ_[p] //
    RealizesMinimalPadicTorsionForm p hpOdd q L}

end LeanCategories.Lattices.Valued
