/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.LinearMaps
public import LeanCategories.Catalogue.Semantics.Modules.Operations
public import Mathlib.LinearAlgebra.Matrix.Notation
public meta import LeanCategories.Catalogue.Semantics.Modules.LinearMaps

@[expose] public section

open CategoryTheory
open CasCatalogue.Modules.LinearMaps

namespace CasCatalogue.Modules.CoordinateLinearityTests

universe u v w

/-- Every dimension remains arbitrary. The two prefix coordinates and the whole
tail use scalar multiples, negation, subtraction, and addition in the selected module. -/
example (n : ℕ) (R : CommRingCat.{u}) (M : ModuleCat.{v} R)
    (a b : R) (i j : Fin n) :
    IsLinearMap R (fun x : Fin n → M =>
      Matrix.vecCons (a • x i - b • x j)
        (Matrix.vecCons (-(x j)) (fun k : Fin n => x k + x k))) := by
  run_tac linearEvidence

/-- Arbitrary index types need no enumeration. Products and finite vectors can
be nested while keeping their coordinate formulas and selected scalars. -/
example {ι : Type w} (R : CommRingCat.{u}) (M : ModuleCat.{v} R)
    (a b : R) (i j : ι) :
    IsLinearMap R (fun x : ι → M =>
      ((fun k : ι => a • x k - b • x i), ![-(x j), x i + x j])) := by
  run_tac linearEvidence

/-- Bundled module maps and their actual composition already provide the full
laws over arbitrary rings, without an assumption of commutativity. -/
example (R : RingCat.{u}) (M N P : ModuleCat.{v} R)
    (f : M ⟶ N) (g : N ⟶ P) :
    IsLinearMap R (M := M) (M₂ := P) (fun x : M => (f ≫ g).hom x) := by
  run_tac linearEvidence

/-- The published application morphism retains the same whole module map. -/
example (R : RingCat.{u}) (M N : ModuleCat.{v} R) (f : M ⟶ N) :
    IsLinearMap R (M := M) (M₂ := N) (fun x : M =>
      ConcreteCategory.hom (C := Type v) (linearApplication R M N) (f, x)) := by
  run_tac linearEvidence

/-- The additive-group scalar-action morphism has its exact point action. Its
linearity here uses the selected commutative scalar structure. -/
example (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (a : R) :
    IsLinearMap R (M := M) (M₂ := M) (fun x : M => (M.smul a).hom x) := by
  run_tac linearEvidence

/-- Restriction of scalars retains the actual module and selected base action. -/
example (R : CommRingCat.{0}) (S : RingCat.{0})
    (q : (forget₂ CommRingCat RingCat).obj R ⟶ S) (N : ModuleCat.{0} S) (a : R) :
    let M := (ModuleCat.restrictScalars q.hom).obj N
    IsLinearMap R (M := M) (M₂ := M) (fun x : M => (M.smul a).hom x) := by
  run_tac linearEvidence

/-- The public uncurried scalar-action declaration is read at that same
restricted module, not at the carrier or original scalar ring. -/
example (R : CommRingCat.{0}) (S : RingCat.{0})
    (q : (forget₂ CommRingCat RingCat).obj R ⟶ S) (N : ModuleCat.{0} S) (a : R) :
    let M := (ModuleCat.restrictScalars q.hom).obj N
    IsLinearMap R (M := M) (M₂ := M) (fun x : M =>
      ConcreteCategory.hom (C := Type)
        (Operations.scalarAction ((forget₂ CommRingCat RingCat).obj R) M) (a, x)) := by
  run_tac linearEvidence

/-- The reindexed whole morphism is admitted over the exact new scalar ring. -/
example (R S : RingCat.{u}) (q : R ⟶ S) (N P : ModuleCat.{v} S) (f : N ⟶ P) :
    IsLinearMap R
      (M := (ModuleCat.restrictScalars q.hom).obj N)
      (M₂ := (ModuleCat.restrictScalars q.hom).obj P)
      (fun x => ((ModuleCat.restrictScalars q.hom).map f).hom x) := by
  run_tac linearEvidence

/-- A nonzero affine coordinate violates the complete map-zero law. -/
theorem affine_not_linear :
    ¬ IsLinearMap ℚ (fun x : ℚ => ![x + 1, -x]) := by
  intro h
  have impossible := congrFun h.map_zero 0
  norm_num at impossible

/-- A quadratic coordinate violates addition preservation. -/
theorem quadratic_not_linear :
    ¬ IsLinearMap ℚ (fun x : ℚ => ![x * x, -x]) := by
  intro h
  have impossible := congrFun (h.map_add 1 1) 0
  norm_num at impossible

/-- The new structural rules cannot admit either nonlinear vector. -/
example : True := by
  fail_if_success
    have : IsLinearMap ℚ (fun x : ℚ => ![x + 1, -x]) := by
      run_tac linearEvidence
  fail_if_success
    have : IsLinearMap ℚ (fun x : ℚ => ![x * x, -x]) := by
      run_tac linearEvidence
  trivial

/-- Being an additive-group scalar-action morphism does not make a noncentral
scalar linear over the original noncommutative scalar ring. -/
theorem noncentral_action_not_linear (R : RingCat.{u}) (a b : R)
    (noncommute : a * b ≠ b * a) :
    ¬ IsLinearMap R (fun x : R => ((ModuleCat.of R R).smul a).hom x) := by
  intro h
  have impossible := h.map_smul b 1
  change a * (b * 1) = b * (a * 1) at impossible
  exact noncommute (by simpa only [mul_one] using impossible)

/-- The noncommutative boundary is realized by two explicit matrix units. -/
example : ¬ IsLinearMap (Matrix (Fin 2) (Fin 2) ℤ)
    (fun x : Matrix (Fin 2) (Fin 2) ℤ =>
      ((ModuleCat.of (Matrix (Fin 2) (Fin 2) ℤ)
        (Matrix (Fin 2) (Fin 2) ℤ)).smul !![0, 1; 0, 0]).hom x) := by
  apply noncentral_action_not_linear
    (RingCat.of (Matrix (Fin 2) (Fin 2) ℤ)) !![0, 1; 0, 0] !![0, 0; 1, 0]
  intro h
  have impossible := congrArg (fun x : Matrix (Fin 2) (Fin 2) ℤ => x 0 0) h
  change (1 : ℤ) = 0 at impossible
  exact (by decide : (1 : ℤ) ≠ 0) impossible

/-- No unconditional scalar-action admission is introduced. -/
example (R : RingCat.{u}) (a b : R) (_noncommute : a * b ≠ b * a) : True := by
  fail_if_success
    have : IsLinearMap R (fun x : R => ((ModuleCat.of R R).smul a).hom x) := by
      run_tac linearEvidence
  trivial

end CasCatalogue.Modules.CoordinateLinearityTests
