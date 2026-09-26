/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.RadicalData
public import Mathlib.GroupTheory.Complement

/-!
# Levi decomposition data

Definition-level reference port for Humphreys FC16-C10-U041.

For a parabolic subgroup `P`, let `V = R_u(P)`.  A subgroup `L ≤ P` is a
Levi factor when `L` is reductive and `P` is the internal semidirect product
of `L` and `V`.  This file records that predicate using Mathlib's internal
complement relation.  Existence and conjugacy of Levi factors are results
and are not included.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A Levi decomposition of `P` with Levi factor `L`.

The predicate says that `L` lies in `P`, is reductive, and complements the
normal unipotent radical inside `P`.  `Subgroup.IsComplement'` is precisely
the unique multiplication factorization predicate. -/
def IsLeviDecomposition
    (isUnipotentElement : G → Prop) (P L : Subgroup G) : Prop :=
  L ≤ P ∧
    IsReductiveGroup (G := L) (fun l : L => isUnipotentElement l.1) ∧
    ∃ V : Subgroup P,
      IsUnipotentRadical (G := P) (fun p : P => isUnipotentElement p.1) V ∧
      V.Normal ∧
      (L.comap P.subtype).IsComplement' V

/-- A Levi factor is a subgroup furnishing a Levi decomposition. -/
def IsLeviFactor
    (isUnipotentElement : G → Prop) (P L : Subgroup G) : Prop :=
  IsLeviDecomposition isUnipotentElement P L

end LeanCategories.AlgebraicGeometry
