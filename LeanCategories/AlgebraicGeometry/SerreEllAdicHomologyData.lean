/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.RelativePicardData
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RepresentationTheory.Basic

/-!
# Serre's ell-adic curve-homology data

Definition-level realization data for Serre FC10-C06-U034.

Serre fixes a prime ell different from the characteristic, takes the three
ell-adic homology modules of a smooth projective curve, identifies degree zero
and degree two with the ell-adic integers, and identifies degree one with the
ell-adic Tate module of the Jacobian. The Galois/deck group acts on the three
modules, giving the three representations whose traces are denoted h_i.

Pinned Mathlib currently supplies pro-etale ell-adic cohomology only as
additive groups, and there is no general algebraic-curve Jacobian/Tate-module
owner. The local FC06 owner supplies the exact relative Picard-zero
presentation. This file therefore records the irreducible source-specific
presentation needed here:

* a candidate module with projections to the ell-power torsion of the
  Jacobian point group;
* the exact inverse-limit predicate characterizing those projections;
* three ell-adic modules with G-actions;
* the source comparison predicate H_0 = Z_ell, H_1 = T_ell(J),
  H_2 = Z_ell.

No existence of a Jacobian, Picard group law, finite-freeness theorem,
comparison theorem, equivariance theorem, or Euler/genus identity is proved
here. Those are result content outside Sweep III.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open LeanCategories.Schemes

namespace LeanCategories.AlgebraicGeometry

universe u v

/-- The source tensor-product graph on the already-recorded relative Picard
zero quotient.

This is deliberately a relation rather than an operation: constructing tensor
products inside the selected quotient and proving that they are independent of
representatives are result-layer obligations. -/
def RelativePicardZeroTensorClassData
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product)
    (P : RelativePicardZeroCandidateData D)
    (a b c : RelativePicardZeroData (D := D) P) : Prop :=
  ∃ L M N : RelativePicardZeroSheafData D,
    P.classOf L = a ∧
    P.classOf M = b ∧
    P.classOf N = c ∧
    Nonempty
      (N.sheaf ≅ schemeModuleTensor L.sheaf M.sheaf)

/-- Exact source specification of the Jacobian point-group law at the chosen
test scheme: the carrier is Pic^0, and addition is induced by tensor product
of degree-zero line-bundle classes.

Totality and uniqueness of the tensor graph are stated here only as the
specification of the source group law; no witness or quotient-law proof is
constructed in Sweep III. -/
def IsSerreJacobianPointGroupData
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product)
    (P : RelativePicardZeroCandidateData D)
    (J : AddCommGrpCat.{u})
    (classOf : RelativePicardZeroData (D := D) P → J) : Prop :=
  Function.Bijective classOf ∧
  ∀ a b : RelativePicardZeroData (D := D) P,
    ∃! c : RelativePicardZeroData (D := D) P,
      RelativePicardZeroTensorClassData D P a b c ∧
        classOf c = classOf a + classOf b

/-- A candidate for the ell-adic Tate module of the Jacobian point group.

The carrier is already an ell-adic module. The maps remember its finite-level
coordinates in the Jacobian point group. The source inverse-limit condition is
stated separately by IsSerreJacobianTateCandidateData. -/
structure SerreJacobianTateCandidateData
    (ell : Nat) [Fact ell.Prime] (J : AddCommGrpCat.{u}) where
  carrier : ModuleCat.{u} ℤ_[ell]
  projection : (n : Nat) → carrier →+ J

/-- Exact source specification of the compatible ell-power torsion sequences
underlying the Tate module.

The final clause also pins the ell-adic scalar action to the finite-level
residue of the scalar, so an arbitrary module structure on the same inverse
limit carrier does not satisfy the specification. -/
def IsSerreJacobianTateCandidateData
    (ell : Nat) [Fact ell.Prime] (J : AddCommGrpCat.{u})
    (T : SerreJacobianTateCandidateData ell J) : Prop :=
  (∀ x : T.carrier, ∀ n : Nat,
      (ell ^ (n + 1)) • T.projection n x = 0) ∧
  (∀ x : T.carrier, ∀ n : Nat,
      ell • T.projection (n + 1) x = T.projection n x) ∧
  (∀ s : Nat → J,
      (∀ n : Nat, (ell ^ (n + 1)) • s n = 0) →
      (∀ n : Nat, ell • s (n + 1) = s n) →
      ∃! x : T.carrier, ∀ n : Nat, T.projection n x = s n) ∧
  (∀ (a : ℤ_[ell]) (x : T.carrier) (n : Nat),
      ∃ m : Nat,
        (m : ZMod (ell ^ (n + 1))) =
            PadicInt.toZModPow (p := ell) (n + 1) a ∧
        T.projection n (a • x) = m • T.projection n x)

/-- Candidate data for Serre's three ell-adic homology representations.

The relative-Picard datum D is the already-realized FC06-C04-U081 input,
specialized in Serre's application to the geometric-point test scheme.
jacobianPoints is the candidate J-valued point group for that test. -/
structure SerreEllAdicHomologyCandidateData
    (residueChar ell : Nat) [Fact ell.Prime] (_hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product) where
  picardZeroCandidate : RelativePicardZeroCandidateData D
  jacobianPoints : AddCommGrpCat.{u}
  picardClass :
    RelativePicardZeroData (D := D) picardZeroCandidate → jacobianPoints
  tate : SerreJacobianTateCandidateData ell jacobianPoints
  homology : Fin 3 → ModuleCat.{u} ℤ_[ell]
  action : ∀ i : Fin 3, Representation ℤ_[ell] G (homology i)

/-- Source comparison predicate for Serre FC10-C06-U034.

The Picard comparison identifies the candidate Jacobian test-point carrier
with the already-recorded Picard-zero quotient. The three remaining clauses
are precisely the degree-zero, degree-one/Tate, and degree-two carrier
identifications. No theorem that these comparisons exist is asserted here. -/
def IsSerreEllAdicHomologyData
    (residueChar ell : Nat) [Fact ell.Prime] (hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product)
    (P : SerreEllAdicHomologyCandidateData residueChar ell hEll G D) : Prop :=
  IsSerreJacobianPointGroupData D P.picardZeroCandidate
      P.jacobianPoints P.picardClass ∧
  IsSerreJacobianTateCandidateData ell P.jacobianPoints P.tate ∧
  Nonempty ((P.homology 0 : Type u) ≃ₗ[ℤ_[ell]] ℤ_[ell]) ∧
  Nonempty ((P.homology 1 : Type u) ≃ₗ[ℤ_[ell]] P.tate.carrier) ∧
  Nonempty ((P.homology 2 : Type u) ≃ₗ[ℤ_[ell]] ℤ_[ell])

/-- There is always ambient candidate data, allowing the source presentation
to be named without importing an existence theorem into Sweep III. -/
instance
    (residueChar ell : Nat) [Fact ell.Prime] (hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product) :
    Nonempty (SerreEllAdicHomologyCandidateData residueChar ell hEll G D) := by
  let J : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} Int)
  let M : ModuleCat.{u} ℤ_[ell] := ModuleCat.of ℤ_[ell] (ULift.{u} ℤ_[ell])
  refine ⟨{
    picardZeroCandidate := {
      carrier := PUnit
      classOf := fun _ => PUnit.unit
    }
    jacobianPoints := J
    picardClass := fun _ => 0
    tate := {
      carrier := M
      projection := fun _ => 0
    }
    homology := fun _ => M
    action := fun _ => Representation.trivial ℤ_[ell] G M
  }⟩

/-- Serre's ell-adic homology package, selected from its exact source
presentation. The theorem layer proves that the selected candidate satisfies
IsSerreEllAdicHomologyData before it is used as a geometric comparison. -/
def serreEllAdicHomologyCandidateData
    (residueChar ell : Nat) [Fact ell.Prime] (hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product) :
    SerreEllAdicHomologyCandidateData residueChar ell hEll G D :=
  Classical.epsilon (IsSerreEllAdicHomologyData residueChar ell hEll G D)

/-- The degree-i ell-adic homology module in the selected source
presentation. -/
abbrev serreEllAdicHomologyModuleData
    (residueChar ell : Nat) [Fact ell.Prime] (hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product) (i : Fin 3) :
    ModuleCat.{u} ℤ_[ell] :=
  (serreEllAdicHomologyCandidateData residueChar ell hEll G D).homology i

/-- The G-action on degree-i ell-adic homology in the selected source
presentation. -/
abbrev serreEllAdicHomologyRepresentationData
    (residueChar ell : Nat) [Fact ell.Prime] (hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product) (i : Fin 3) :
    Representation ℤ_[ell] G
      (serreEllAdicHomologyModuleData residueChar ell hEll G D i) :=
  (serreEllAdicHomologyCandidateData residueChar ell hEll G D).action i

/-- Serre's raw trace h_i of the degree-i ell-adic representation.

Finite-freeness, which makes this the usual finite-rank character, is a result
clause and is deliberately not proved here. -/
def serreEllAdicHomologyTraceData
    (residueChar ell : Nat) [Fact ell.Prime] (hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product) (i : Fin 3) :
    G → ℤ_[ell] :=
  fun g =>
    LinearMap.trace ℤ_[ell]
      (serreEllAdicHomologyModuleData residueChar ell hEll G D i)
      (serreEllAdicHomologyRepresentationData residueChar ell hEll G D i g)

/-- Serre's virtual trace h = h_0 - h_1 + h_2. -/
def serreEllAdicVirtualTraceData
    (residueChar ell : Nat) [Fact ell.Prime] (hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product) :
    G → ℤ_[ell] :=
  fun g =>
    serreEllAdicHomologyTraceData residueChar ell hEll G D 0 g -
      serreEllAdicHomologyTraceData residueChar ell hEll G D 1 g +
        serreEllAdicHomologyTraceData residueChar ell hEll G D 2 g

/-- The source Euler-characteristic datum h(1).

Its identification with 2 - 2g is a result clause and remains outside Sweep
III. -/
def serreEllAdicEulerCharacteristicData
    (residueChar ell : Nat) [Fact ell.Prime] (hEll : ell ≠ residueChar)
    (G : Type v) [Group G]
    {Y T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData Y T product) : ℤ_[ell] :=
  serreEllAdicVirtualTraceData residueChar ell hEll G D 1

end LeanCategories.AlgebraicGeometry
