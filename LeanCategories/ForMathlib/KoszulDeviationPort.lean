/-
Copyright (c) 2026 Nailin Guan, Jingting Wang, Yi Yuan, Yongle Hu.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from mathlib4 PR #34913 at c7780ed427bbed31ee0c430a5594ed5ea4c7d5b5.
-/
module

public import LeanCategories.ForMathlib.KoszulHomotopyPort
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Canonical Koszul deviations for Noetherian local rings

Minimal port of the construction used by mathlib4 PR #34913. The maximal
ideal is equipped with Mathlib's canonical minimal finite generating set;
the associated Koszul homology is annihilated by the maximal ideal and
therefore carries its canonical residue-field module structure.
-/

@[expose] public noncomputable section

open IsLocalRing CategoryTheory

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The canonical Koszul complex on Mathlib's minimal finite generating set
of the maximal ideal. -/
noncomputable abbrev matsumuraKoszulAlgebraData :=
  koszulComplex.ofList
    (Submodule.FG.finite_generators (maximalIdeal R).fg_of_isNoetherianRing).toFinset.toList

/-- The maximal ideal annihilates every homology group of the canonical
minimal-generator Koszul complex. -/
lemma matsumuraKoszulAlgebraData_annihilator_homology (i : ℕ) :
    maximalIdeal R ≤ Module.annihilator R ((matsumuraKoszulAlgebraData R).homology i) := by
  apply le_of_eq_of_le _ (koszulComplex.ofList_ideal_annihilator_homology _ i)
  simpa [Ideal.ofList] using (maximalIdeal R).span_generators.symm

noncomputable instance matsumuraKoszulHomologyResidueModule (i : ℕ) :
    Module (ResidueField R) ((matsumuraKoszulAlgebraData R).homology i) :=
  Module.IsTorsionBySet.module (fun x a ↦
    Module.mem_annihilator.mp
      (matsumuraKoszulAlgebraData_annihilator_homology R i a.2) x)

noncomputable instance matsumuraKoszulHomologyScalarTower (i : ℕ) :
    IsScalarTower R (ResidueField R) ((matsumuraKoszulAlgebraData R).homology i) :=
  IsScalarTower.of_compHom R (ResidueField R) ((matsumuraKoszulAlgebraData R).homology i)

noncomputable instance matsumuraKoszulDegreeFinite (i : ℕ) :
    Module.Finite R ((matsumuraKoszulAlgebraData R).X i) :=
  exteriorPower.instFinite

noncomputable instance matsumuraKoszulHomologyFinite (i : ℕ) :
    Module.Finite R ((matsumuraKoszulAlgebraData R).homology i) := by
  apply (Module.Finite.equiv_iff
    ((matsumuraKoszulAlgebraData R).sc i).moduleCatHomologyIso.toLinearEquiv).mpr
  have : Module.Finite R (HomologicalComplex.sc (matsumuraKoszulAlgebraData R) i).X₂ :=
    exteriorPower.instFinite
  exact Module.Finite.quotient R _

noncomputable instance matsumuraKoszulHomologyResidueFinite (i : ℕ) :
    Module.Finite (ResidueField R) ((matsumuraKoszulAlgebraData R).homology i) :=
  Module.Finite.of_restrictScalars_finite R _ _

end
