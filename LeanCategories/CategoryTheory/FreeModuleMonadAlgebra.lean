/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Algebra

@[expose] public noncomputable section

open _root_.CategoryTheory
open _root_.ModuleCat

namespace LeanCategories.CategoryTheory

universe u

variable (R : Type u) [Ring R]

/-- The monad on types induced by the free/forgetful adjunction for `R`-modules.
This is the monad in FC03-C05-U015. -/
noncomputable abbrev FreeModuleMonad := (_root_.ModuleCat.adj R).toMonad

variable {R}

/-- The evaluation map of an algebra for the free-module monad. -/
noncomputable def FreeModuleAlgebra.eval (A : (FreeModuleMonad R).Algebra) :
    (A.A →₀ R) → A.A := fun v => A.a v

namespace FreeModuleAlgebra

/-- The unit of the free-module monad inserts a generator with coefficient one. -/
theorem eta_apply (X : Type u) (x : X) :
    (FreeModuleMonad R).η.app X x = Finsupp.single x 1 := by
  rfl

/-- The multiplication of the free-module monad evaluates a finite linear combination of
finite linear combinations. -/
theorem mu_apply (X : Type u) (V : (X →₀ R) →₀ R) :
    (FreeModuleMonad R).μ.app X V = V.sum (fun v r => r • v) := by
  rfl

/-- The free-module monad pushes coefficients forward along a function. -/
@[simp]
theorem map_apply {X Y : Type u} (f : X ⟶ Y) (v : X →₀ R) :
    (FreeModuleMonad R).map f v = Finsupp.mapDomain f v := by
  rfl

/-- The Eilenberg--Moore unit law says that evaluating the singleton coefficient-one
combination returns the original point. -/
@[simp]
theorem eval_single_one (A : (FreeModuleMonad R).Algebra) (x : A.A) :
    eval A (Finsupp.single x 1) = x := by
  have h := ConcreteCategory.congr_hom A.unit x
  change eval A ((FreeModuleMonad R).η.app A.A x) = x at h
  rw [eta_apply] at h
  exact h

/-- The Eilenberg--Moore associativity law is evaluation of a flattened finite combination. -/
theorem eval_flatten (A : (FreeModuleMonad R).Algebra) (V : (A.A →₀ R) →₀ R) :
    eval A (V.sum fun v r => r • v) = eval A (Finsupp.mapDomain (eval A) V) := by
  have h := ConcreteCategory.congr_hom A.assoc V
  change eval A ((FreeModuleMonad R).μ.app A.A V) =
    eval A ((FreeModuleMonad R).map A.a V) at h
  rw [mu_apply] at h
  change eval A (V.sum fun v r => r • v) = eval A (Finsupp.mapDomain (eval A) V) at h
  exact h

/-- Evaluation respects addition after addition on the carrier is reconstructed from the algebra. -/
theorem eval_add_formula (A : (FreeModuleMonad R).Algebra) (v w : A.A →₀ R) :
    eval A (v + w) =
      eval A (Finsupp.single (eval A v) 1 + Finsupp.single (eval A w) 1) := by
  let V : (A.A →₀ R) →₀ R := Finsupp.single v 1 + Finsupp.single w 1
  have h := eval_flatten A V
  dsimp [V] at h
  have hsum : (Finsupp.single v (1 : R) + Finsupp.single w (1 : R)).sum
      (fun (a : A.A →₀ R) (r : R) => r • a) = v + w := by
    rw [Finsupp.sum_add_index'
      (h := fun (a : A.A →₀ R) (r : R) => r • a)]
    · rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
      · simp
      · exact zero_smul R w
      · exact zero_smul R v
    · intro a
      exact zero_smul R a
    · intro a r s
      exact add_smul r s a
  have hmap :
      Finsupp.mapDomain (eval A)
          (Finsupp.single v (1 : R) + Finsupp.single w (1 : R)) =
        Finsupp.single (eval A v) 1 + Finsupp.single (eval A w) 1 := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  have h' : eval A (v + w) =
      eval A (Finsupp.mapDomain (eval A)
        (Finsupp.single v (1 : R) + Finsupp.single w (1 : R))) :=
    (congrArg (eval A) hsum).symm.trans h
  exact h'.trans (congrArg (eval A) hmap)

/-- Evaluation respects scalar multiplication after scalar multiplication on the carrier is
reconstructed from the algebra. -/
theorem eval_smul_formula (A : (FreeModuleMonad R).Algebra) (r : R) (v : A.A →₀ R) :
    eval A (r • v) = eval A (Finsupp.single (eval A v) r) := by
  let V : (A.A →₀ R) →₀ R := Finsupp.single v r
  have h := eval_flatten A V
  dsimp [V] at h
  simpa using h

noncomputable def zeroOfEval {A : Type u} (e : (A →₀ R) → A) : A := e 0

noncomputable def addOfEval {A : Type u} (e : (A →₀ R) → A) (x y : A) : A :=
  e (Finsupp.single x 1 + Finsupp.single y 1)

noncomputable def negOfEval {A : Type u} (e : (A →₀ R) → A) (x : A) : A :=
  e (Finsupp.single x (-1))

noncomputable def smulOfEval {A : Type u} (e : (A →₀ R) → A) (r : R) (x : A) : A :=
  e (Finsupp.single x r)

@[instance_reducible]
noncomputable def addCommGroupOfEval {A : Type u}
    (e : (A →₀ R) → A)
    (hunit : ∀ x, e (Finsupp.single x 1) = x)
    (hadd : ∀ v w, e (v + w) =
      e (Finsupp.single (e v) 1 + Finsupp.single (e w) 1)) : AddCommGroup A := by
  letI : Zero A := ⟨zeroOfEval e⟩
  letI : Add A := ⟨addOfEval e⟩
  letI : Neg A := ⟨negOfEval e⟩
  have hzadd : ∀ x : A, 0 + x = x := by
    intro x
    change e (Finsupp.single (e 0) 1 + Finsupp.single x 1) = x
    rw [← hunit x]
    exact (hadd 0 (Finsupp.single x 1)).symm.trans (by simp)
  have hassoc : ∀ x y z : A, (x + y) + z = x + (y + z) := by
    intro x y z
    let vx : A →₀ R := Finsupp.single x 1
    let vy : A →₀ R := Finsupp.single y 1
    let vz : A →₀ R := Finsupp.single z 1
    change e (Finsupp.single (e (vx + vy)) 1 + Finsupp.single z 1) =
      e (Finsupp.single x 1 + Finsupp.single (e (vy + vz)) 1)
    rw [← hunit z, ← hunit x, ← hadd (vx + vy) vz, ← hadd vx (vy + vz), add_assoc]
  have hneg : ∀ x : A, -x + x = 0 := by
    intro x
    let vn : A →₀ R := Finsupp.single x (-1)
    let vx : A →₀ R := Finsupp.single x 1
    change e (Finsupp.single (e vn) 1 + Finsupp.single x 1) = e 0
    rw [← hunit x, ← hadd vn vx]
    congr 1
    ext a
    by_cases ha : a = x
    · subst a
      simp [vn, vx]
    · simp [vn, vx]
  let hgroup : AddGroup A := AddGroup.ofLeftAxioms hassoc hzadd hneg
  letI : AddGroup A := hgroup
  exact
    { toAddGroup := hgroup
      add_comm := by
        intro x y
        change e (Finsupp.single x 1 + Finsupp.single y 1) =
          e (Finsupp.single y 1 + Finsupp.single x 1)
        rw [add_comm] }

/-- Given an evaluator satisfying the three consequences of the Eilenberg--Moore laws,
construct the corresponding `R`-module on the same carrier. -/
noncomputable def moduleCatOfEval {A : Type u}
    (e : (A →₀ R) → A)
    (hunit : ∀ x, e (Finsupp.single x 1) = x)
    (hadd : ∀ v w, e (v + w) =
      e (Finsupp.single (e v) 1 + Finsupp.single (e w) 1))
    (hsmul : ∀ r v, e (r • v) = e (Finsupp.single (e v) r)) :
    _root_.ModuleCat.{u} R := by
  letI : AddCommGroup A := addCommGroupOfEval e hunit hadd
  letI : SMul R A := ⟨smulOfEval e⟩
  have hone : ∀ x : A, (1 : R) • x = x := by
    intro x
    change e (Finsupp.single x 1) = x
    exact hunit x
  have hmul : ∀ (r s : R) (x : A), (r * s) • x = r • (s • x) := by
    intro r s x
    change e (Finsupp.single x (r * s)) =
      e (Finsupp.single (e (Finsupp.single x s)) r)
    rw [← hsmul r (Finsupp.single x s)]
    congr 1
    simp
  have hszero : ∀ r : R, r • (0 : A) = 0 := by
    intro r
    change e (Finsupp.single (e 0) r) = e 0
    rw [← hsmul r 0]
    simp
  have hsadd : ∀ (r : R) (x y : A), r • (x + y) = r • x + r • y := by
    intro r x y
    change e (Finsupp.single (e (Finsupp.single x 1 + Finsupp.single y 1)) r) =
      e (Finsupp.single (e (Finsupp.single x r)) 1 +
        Finsupp.single (e (Finsupp.single y r)) 1)
    rw [← hsmul r (Finsupp.single x 1 + Finsupp.single y 1)]
    rw [smul_add]
    simpa using hadd (Finsupp.single x r) (Finsupp.single y r)
  let hdistrib : DistribMulAction R A :=
    { smul := smulOfEval e
      one_smul := hone
      mul_smul := hmul
      smul_zero := hszero
      smul_add := hsadd }
  letI : DistribMulAction R A := hdistrib
  let hmodule : Module R A := Module.mk
    (fun r s x => by
      change e (Finsupp.single x (r + s)) =
        e (Finsupp.single (e (Finsupp.single x r)) 1 +
          Finsupp.single (e (Finsupp.single x s)) 1)
      rw [← hadd (Finsupp.single x r) (Finsupp.single x s)]
      congr 1
      ext a
      by_cases ha : a = x <;> simp [ha])
    (fun x => by
      change e (Finsupp.single x 0) = e 0
      simp)
  letI : Module R A := hmodule
  exact _root_.ModuleCat.of R A

/-- FC03-C05-U015: an algebra for the free `R`-module monad canonically reconstructs an
`R`-module structure on the same carrier. -/
noncomputable def toModule (A : (FreeModuleMonad R).Algebra) : _root_.ModuleCat.{u} R :=
  moduleCatOfEval (eval A) (eval_single_one A) (eval_add_formula A) (eval_smul_formula A)

/-- In the module reconstructed from an Eilenberg--Moore algebra, scalar multiplication is
exactly evaluation of a singleton finite combination. -/
@[simp]
theorem toModule_smul (A : (FreeModuleMonad R).Algebra) (r : R) (x : (toModule A : Type u)) :
    r • x = eval A (Finsupp.single x r) := by
  rfl

/-- Conversely, the Eilenberg--Moore algebra produced from an `R`-module by the free/forgetful
comparison evaluates an arbitrary Finsupp as its finite `R`-linear combination. -/
theorem comparison_action (M : _root_.ModuleCat.{u} R) (v : M →₀ R) :
    ((Monad.comparison (_root_.ModuleCat.adj R)).obj M).a v =
      v.sum (fun x r => r • x) := by
  rfl

end FreeModuleAlgebra
end LeanCategories.CategoryTheory
