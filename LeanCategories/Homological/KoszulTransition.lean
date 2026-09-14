/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.KoszulExteriorDescription
public import LeanCategories.Homological.KoszulHomology

/-!
# Transition maps between Koszul complexes of powers

Weibel, *An Introduction to Homological Algebra* (1994), §4.6, pp. 115--119
(FC05-C04-U080).

For a central sequence `x`, the map `K(x^(i+1)) → K(x^i)` multiplies the
wedge basis element `e_I` by the product of the `x_j` with `j ∈ I`.  These
maps induce the inverse system on Koszul homology and, contravariantly, the
direct system on Koszul cohomology.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite

universe u

variable (R : Type u) [Ring R]

/-- The coordinatewise `m`th power of a finite sequence. -/
def koszulPowerSequence {n : ℕ} (x : Fin n → R) (m : ℕ) : Fin n → R :=
  fun j => x j ^ m

/-- Powers of a central sequence are central. -/
theorem isCentralSequence_power {n : ℕ} {x : Fin n → R}
    (hx : IsCentralSequence R x) (m : ℕ) :
    IsCentralSequence R (koszulPowerSequence R x m) := by
  intro j r
  induction m with
  | zero => simp [koszulPowerSequence]
  | succ m ih =>
      simp only [koszulPowerSequence, pow_succ]
      have ih' : x j ^ m * r = r * x j ^ m := by
        simpa [koszulPowerSequence] using ih
      calc
        x j ^ m * x j * r = x j ^ m * (x j * r) := by rw [mul_assoc]
        _ = x j ^ m * (r * x j) := by rw [hx j r]
        _ = (x j ^ m * r) * x j := by rw [mul_assoc]
        _ = (r * x j ^ m) * x j := by rw [ih']
        _ = r * (x j ^ m * x j) := by rw [mul_assoc]

/-- A member of a central sequence, regarded as an element of the center of the ring. -/
def koszulCentralElement {n : ℕ} (x : Fin n → R) (hx : IsCentralSequence R x)
    (j : Fin n) : Subring.center R :=
  ⟨x j, Subring.mem_center_iff.mpr fun r => (hx j r).symm⟩

/-- Product in the center of the sequence entries indexed by a wedge symbol. -/
def koszulTransitionCenterCoefficient {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulWedgeIndex n p) : Subring.center R :=
  ∏ j ∈ s.1, koszulCentralElement R x hx j

/-- The transition coefficient, viewed back in the ambient ring. -/
def koszulTransitionCoefficient {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulWedgeIndex n p) : R :=
  koszulTransitionCenterCoefficient R x hx s

/-- Extracting one index from the transition coefficient removes exactly its central factor. -/
theorem koszulTransitionCoefficient_erase {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulWedgeIndex n (p + 1))
    (j : Fin n) (hj : j ∈ s.1) :
    x j * koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj) =
      koszulTransitionCoefficient R x hx s := by
  exact congrArg Subtype.val
    (Finset.mul_prod_erase s.1 (fun k => koszulCentralElement R x hx k) hj)

/-- Every transition coefficient remains central in the ambient ring. -/
theorem koszulTransitionCoefficient_commute {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulWedgeIndex n p) (r : R) :
    koszulTransitionCoefficient R x hx s * r =
      r * koszulTransitionCoefficient R x hx s := by
  exact (Subring.mem_center_iff.mp (koszulTransitionCenterCoefficient R x hx s).2 r).symm

/-- The coefficient identity which makes the power transition a chain map. -/
theorem koszulTransitionCoefficient_mul_power {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulWedgeIndex n (p + 1))
    (j : Fin n) (hj : j ∈ s.1) (i : ℕ) :
    koszulTransitionCoefficient R x hx s * x j ^ i =
      x j ^ (i + 1) *
        koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj) := by
  rw [← koszulTransitionCoefficient_erase R x hx s j hj]
  calc
    (x j * koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj)) * x j ^ i =
        x j *
          (koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj) * x j ^ i) := by
            rw [mul_assoc]
    _ = x j *
          (x j ^ i * koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj)) := by
            rw [koszulTransitionCoefficient_commute R x hx]
    _ = (x j * x j ^ i) *
          koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj) := by
            rw [mul_assoc]
    _ = x j ^ (i + 1) *
          koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj) := by
            rw [pow_succ']

/-- Degree-`p` part of the canonical transition `K(x^(i+1)) → K(x^i)`: multiply each wedge
basis symbol by the product of the `x_j` occurring in that wedge. -/
noncomputable def koszulPowerTransitionDegreeMap {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) :
    KoszulDegree R n p →ₗ[R] KoszulDegree R n p :=
  Finsupp.linearCombination R fun s =>
    koszulTransitionCoefficient R x hx s • koszulWedgeSymbol R s

@[simp]
theorem koszulPowerTransitionDegreeMap_wedge {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulWedgeIndex n p) :
    koszulPowerTransitionDegreeMap R x hx (koszulWedgeSymbol R s) =
      koszulTransitionCoefficient R x hx s • koszulWedgeSymbol R s := by
  simp [koszulPowerTransitionDegreeMap, koszulWedgeSymbol]

@[simp]
theorem koszulPowerTransitionDegreeMap_single {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulWedgeIndex n p) (r : R) :
    koszulPowerTransitionDegreeMap R x hx (Finsupp.single s r) =
      r • (koszulTransitionCoefficient R x hx s • koszulWedgeSymbol R s) := by
  simp [koszulPowerTransitionDegreeMap]

/-- Compatibility of the transition coefficient with one Koszul boundary summand. -/
theorem koszulTransitionBoundaryCoefficient {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (s : KoszulWedgeIndex n (p + 1))
    (j : Fin n) (hj : j ∈ s.1) (i : ℕ) :
    koszulTransitionCoefficient R x hx s *
        koszulBoundaryCoefficient R (koszulPowerSequence R x i) s j =
      koszulBoundaryCoefficient R (koszulPowerSequence R x (i + 1)) s j *
        koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj) := by
  simp only [koszulBoundaryCoefficient, koszulPowerSequence]
  calc
    koszulTransitionCoefficient R x hx s *
        ((-1 : R) ^ koszulPosition s j * x j ^ i) =
      (koszulTransitionCoefficient R x hx s *
          (-1 : R) ^ koszulPosition s j) * x j ^ i := by rw [mul_assoc]
    _ = (((-1 : R) ^ koszulPosition s j) *
          koszulTransitionCoefficient R x hx s) * x j ^ i := by
            rw [koszulTransitionCoefficient_commute R x hx]
    _ = ((-1 : R) ^ koszulPosition s j) *
          (koszulTransitionCoefficient R x hx s * x j ^ i) := by rw [mul_assoc]
    _ = ((-1 : R) ^ koszulPosition s j) *
          (x j ^ (i + 1) *
            koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj)) := by
              rw [koszulTransitionCoefficient_mul_power R x hx s j hj i]
    _ = (((-1 : R) ^ koszulPosition s j) * x j ^ (i + 1)) *
          koszulTransitionCoefficient R x hx (koszulEraseIndex s j hj) := by rw [mul_assoc]

/-- The degree maps for the power transition commute with the Koszul differentials. -/
theorem koszulPowerTransitionDegreeMap_boundaryData {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (i : ℕ) (s : KoszulWedgeIndex n (p + 1)) :
    koszulBoundaryLinearMap R (koszulPowerSequence R x i)
        (koszulPowerTransitionDegreeMap R x hx (koszulWedgeSymbol R s)) =
      koszulPowerTransitionDegreeMap R x hx
        (koszulBoundaryData R (koszulPowerSequence R x (i + 1)) s) := by
  rw [koszulPowerTransitionDegreeMap_wedge, map_smul]
  simp only [koszulWedgeSymbol, koszulBoundaryLinearMap_single, one_smul]
  rw [koszulBoundaryData, koszulBoundaryData]
  simp only [Finset.smul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [koszulPowerTransitionDegreeMap_single, koszulWedgeSymbol,
    Finsupp.smul_single', smul_smul, mul_one] using congrArg
      (fun c : R => c • koszulWedgeSymbol R (koszulEraseIndex s j.1 j.2))
      (koszulTransitionBoundaryCoefficient R x hx s j.1 j.2 i)

theorem koszulPowerTransitionDegreeMap_comm {n p : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (i : ℕ) :
    (koszulBoundaryLinearMap R (koszulPowerSequence R x i) (p := p)).comp
        (koszulPowerTransitionDegreeMap R x hx (p := p + 1)) =
      (koszulPowerTransitionDegreeMap R x hx (p := p)).comp
        (koszulBoundaryLinearMap R (koszulPowerSequence R x (i + 1)) (p := p)) := by
  apply Finsupp.lhom_ext
  intro s r
  change koszulBoundaryLinearMap R (koszulPowerSequence R x i)
      (koszulPowerTransitionDegreeMap R x hx (Finsupp.single s r)) =
    koszulPowerTransitionDegreeMap R x hx
      (koszulBoundaryLinearMap R (koszulPowerSequence R x (i + 1)) (Finsupp.single s r))
  rw [show Finsupp.single s r = r • koszulWedgeSymbol R s by simp [koszulWedgeSymbol]]
  simpa only [map_smul, koszulWedgeSymbol, koszulBoundaryLinearMap_single, one_smul] using
    congrArg (fun z => r • z)
    (koszulPowerTransitionDegreeMap_boundaryData R x hx i s)

/-- The canonical chain map `K(x^(i+1)) → K(x^i)` on the canonical Koszul complexes. -/
noncomputable def koszulPowerTransitionMap {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (i : ℕ) :
    koszulComplex R (koszulPowerSequence R x (i + 1))
        (isCentralSequence_power R hx (i + 1)) ⟶
      koszulComplex R (koszulPowerSequence R x i)
        (isCentralSequence_power R hx i) :=
  ChainComplex.ofHom
    (fun p => ModuleCat.ofHom (koszulPowerTransitionDegreeMap R x hx (p := p)))
    (fun p => by
      apply ModuleCat.hom_ext
      simp only [koszulComplex_d]
      exact koszulPowerTransitionDegreeMap_comm R x hx i)

/-- A source-faithful transition map `K(x^(i+1)) → K(x^i)`. -/
structure KoszulPowerTransition {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (i : ℕ)
    (Knext : KoszulComplexRealization R (koszulPowerSequence R x (i + 1))
      (isCentralSequence_power R hx (i + 1)))
    (Kcurr : KoszulComplexRealization R (koszulPowerSequence R x i)
      (isCentralSequence_power R hx i)) where
  /-- The transition chain map. -/
  map : Knext.complex ⟶ Kcurr.complex
  /-- On a wedge basis symbol `e_I`, multiply by `∏_{j∈I} x_j`. -/
  map_wedge : ∀ (p : ℕ) (s : KoszulWedgeIndex n p),
    (Kcurr.degreeIso p).hom
        (map.f p ((Knext.degreeIso p).inv (koszulWedgeSymbol R s))) =
      koszulTransitionCoefficient R x hx s • koszulWedgeSymbol R s

/-- The canonical transition between the canonical realizations of successive powers. -/
noncomputable def canonicalKoszulPowerTransition {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (i : ℕ) :
    KoszulPowerTransition R x hx i
      (canonicalKoszulComplexRealization R (koszulPowerSequence R x (i + 1))
        (isCentralSequence_power R hx (i + 1)))
      (canonicalKoszulComplexRealization R (koszulPowerSequence R x i)
        (isCentralSequence_power R hx i)) where
  map := koszulPowerTransitionMap R x hx i
  map_wedge := by
    intro p s
    simp only [canonicalKoszulComplexRealization, Iso.refl_hom, Iso.refl_inv]
    exact koszulPowerTransitionDegreeMap_wedge R x hx s

/-- The induced transition `H_q(x^(i+1),A) → H_q(x^i,A)` on Koszul homology. -/
noncomputable def koszulHomologyTransition {n : ℕ} {x : Fin n → R}
    {hx : IsCentralSequence R x} {i : ℕ}
    {Knext : KoszulComplexRealization R (koszulPowerSequence R x (i + 1))
      (isCentralSequence_power R hx (i + 1))}
    {Kcurr : KoszulComplexRealization R (koszulPowerSequence R x i)
      (isCentralSequence_power R hx i)}
    (T : KoszulPowerTransition R x hx i Knext Kcurr)
    (A : ModuleCat Rᵐᵒᵖ) (q : ℕ) :
    koszulHomologyOf R _ _ Knext A q ⟶ koszulHomologyOf R _ _ Kcurr A q :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) q).map
    (((tensorLeftFunctor R A).mapHomologicalComplex (ComplexShape.down ℕ)).map T.map)

/-- The contravariantly induced map `H^q(x^i,B) → H^q(x^(i+1),B)` on
Koszul cohomology. -/
noncomputable def koszulCohomologyTransition {n : ℕ} {x : Fin n → R}
    {hx : IsCentralSequence R x} {i : ℕ}
    {Knext : KoszulComplexRealization R (koszulPowerSequence R x (i + 1))
      (isCentralSequence_power R hx (i + 1))}
    {Kcurr : KoszulComplexRealization R (koszulPowerSequence R x i)
      (isCentralSequence_power R hx i)}
    (T : KoszulPowerTransition R x hx i Knext Kcurr)
    (B : ModuleCat R) (q : ℕ) :
    koszulCohomologyOf R _ _ Kcurr B q ⟶ koszulCohomologyOf R _ _ Knext B q :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q).map
    (((preadditiveYoneda.obj B).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((HomologicalComplex.opFunctor (ModuleCat R) (ComplexShape.down ℕ)).map T.map.op))

end LeanCategories.Homological
