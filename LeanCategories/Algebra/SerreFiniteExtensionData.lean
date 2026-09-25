/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.ValuationExtensionOrbitData
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Serre finite-extension local data

Definition-level realization of Serre FC10-C04-U002.

For a finite separable extension `L/K`, Serre takes the integral closure of the
valuation ring of `K` in `L`, uses the unique extending discrete valuation,
and then writes down its maximal ideal, residue field, units, ramification
index, and residue degree.  The existence/uniqueness of the extending local
field structure, identification with the integral closure, completeness, and
the equality `e * f = [L : K]` are Chapter-II results.

Sweep III therefore records the exact candidate data and the graph selecting
the source integral closure.  No result-layer theorem is bundled into a
constructor.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

variable {K : Type u} {L : Type v}
  [Field K] [Field L] [Algebra K L]

/-- The canonical ring homomorphism from a base valuation subring to a chosen
valuation extension whose restriction is exactly the base subring. -/
def valuationExtensionRingHomData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A) : A →+* B.1 where
  toFun a := ⟨algebraMap K L a.1, by
    change a.1 ∈ B.1.comap (algebraMap K L)
    rw [B.2]
    exact a.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The source integer ring `A_L`: the integral closure of `A_K` in `L`,
viewed only as a subring of `L` so that the temporary composed algebra
structure does not escape this definition. -/
def serreFiniteExtensionIntegerRingData (A : ValuationSubring K) : Subring L := by
  let f : A →+* L := (algebraMap K L).comp A.toSubring.subtype
  letI : Algebra A L := f.toAlgebra
  exact (integralClosure A L).toSubring

/-- Exact graph selecting the valuation extension whose valuation ring is the
integral closure used by Serre.  The theorem that such a unique extension
exists is deliberately not part of this definition. -/
def IsSerreFiniteExtensionValuationData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A) : Prop :=
  B.1.toSubring = serreFiniteExtensionIntegerRingData A

/-- Serre's extended valuation `v_L`, attached to a candidate valuation
extension. -/
def serreFiniteExtensionValuationData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A) :=
  B.1.valuation

/-- Serre's maximal ideal `p_L`. -/
def serreFiniteExtensionMaximalIdealData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A) : Ideal B.1 :=
  IsLocalRing.maximalIdeal B.1

/-- Serre's residue field `\bar L`. -/
abbrev serreFiniteExtensionResidueFieldData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A) :=
  IsLocalRing.ResidueField B.1

/-- Serre's unit group `U_L`. -/
abbrev serreFiniteExtensionUnitsData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A) :=
  B.1ˣ

/-- The ramification index of the chosen valuation extension, using the
native ideal-theoretic definition from FC10-C01-U041. -/
def serreFiniteExtensionRamificationIndexData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A) : ℕ := by
  let f := valuationExtensionRingHomData A B
  letI : Algebra A B.1 := f.toAlgebra
  exact Ideal.ramificationIdx'
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B.1)

/-- The residue degree of the chosen valuation extension, using the native
quotient-field degree definition from FC10-C01-U042. -/
def serreFiniteExtensionResidueDegreeData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A) : ℕ := by
  let f := valuationExtensionRingHomData A B
  letI : Algebra A B.1 := f.toAlgebra
  exact Ideal.inertiaDeg'
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B.1)

/-- Exact graph for a residue-field map induced by the valuation extension.

This avoids assuming the local-hom theorem merely to state Serre's standing
separability hypothesis. -/
def IsSerreResidueFieldMapData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A)
    (phi : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B.1) : Prop :=
  ∀ a : A,
    phi (IsLocalRing.residue A a) =
      IsLocalRing.residue B.1 (valuationExtensionRingHomData A B a)

/-- Serre's standing hypothesis that the residue extension is separable,
stated as a predicate on an exact candidate residue map. -/
def IsSerreResidueExtensionSeparableData
    (A : ValuationSubring K) (B : ValuationExtensionData (L := L) A)
    (phi : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B.1) : Prop :=
  IsSerreResidueFieldMapData A B phi ∧
    letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B.1) := phi.toAlgebra
    Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B.1)

end LeanCategories.Algebra
