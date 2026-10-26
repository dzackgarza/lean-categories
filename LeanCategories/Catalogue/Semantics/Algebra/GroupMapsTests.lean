/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.GroupMaps
public import LeanCategories.Catalogue.Semantics.Algebra.FiniteGroups
public import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.NormNum
public meta import LeanCategories.Catalogue.Semantics.Algebra.GroupMaps

@[expose] public section

open CategoryTheory
open CasCatalogue.Algebra.GroupMaps

namespace CasCatalogue.Algebra.GroupMapsTests

/-- The law of an existing whole group morphism is retained. -/
example (G H : GrpCat.{0}) (f : G ⟶ H) :
    ∀ a b : G, f.hom (a * b) = f.hom a * f.hom b := by
  run_tac groupEvidence

/-- The selected residue group is commutative, so its entire square map is
admitted. The input is the already published full monoid-power operation. -/
theorem residue_square_law :
    ∀ a b : FiniteGroups.cyclic 5,
      Calculus.power ((forget₂ GrpCat MonCat).obj (FiniteGroups.cyclic 5)) ((a * b), 2) =
        Calculus.power ((forget₂ GrpCat MonCat).obj (FiniteGroups.cyclic 5)) (a, 2) *
          Calculus.power ((forget₂ GrpCat MonCat).obj (FiniteGroups.cyclic 5)) (b, 2) := by
  run_tac groupEvidence

/-- The admitted square is the exact standard monoid homomorphism on the
selected group, not merely a set map with retagged endpoints. -/
theorem residue_square_admission :
    admitGroup (FiniteGroups.cyclic 5) (FiniteGroups.cyclic 5)
      (fun a => Calculus.power
        ((forget₂ GrpCat MonCat).obj (FiniteGroups.cyclic 5)) (a, 2))
      residue_square_law PUnit.unit =
        GrpCat.ofHom (powMonoidHom (α := Multiplicative (ZMod 5)) 2) := by
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro a
  rfl

/-- Multiplicativity of squaring would force a group's whole multiplication
to commute. This law cannot be supplied for arbitrary selected groups. -/
theorem square_law_implies_commutative (G : GrpCat.{0})
    (h : ∀ a b : G, (a * b) ^ 2 = a ^ 2 * b ^ 2) (a b : G) : a * b = b * a := by
  have cancelled := congrArg (fun x : G => a⁻¹ * x * b⁻¹) (h a b)
  simpa [pow_two, mul_assoc] using cancelled.symm

/-- Two transpositions witness failure of the square-map law in a
noncommutative group. -/
theorem permutation_square_not_multiplicative :
    ¬ ∀ a b : Equiv.Perm (Fin 3), (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  intro h
  have impossible := congrArg (fun p : Equiv.Perm (Fin 3) => p 0)
    (h (Equiv.swap 0 1) (Equiv.swap 1 2))
  change (2 : Fin 3) = (0 : Fin 3) at impossible
  exact (by decide : (2 : Fin 3) ≠ 0) impossible

/-- The evidence procedure does not infer multiplicativity from a power
expression whose group lacks the required commutative structure. -/
example : True := by
  fail_if_success
    have : ∀ a b : Equiv.Perm (Fin 3), (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
      run_tac groupEvidence
  trivial

end CasCatalogue.Algebra.GroupMapsTests
