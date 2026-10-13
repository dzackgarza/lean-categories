/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.VermaModuleData
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Central-character graph of a Verma module

Definition-level realization of Humphreys FC14-C06-U043, adapted from
TauCetiProject/TauCeti at
74b1b2b2a25467497550234a92ddfc1322a5903f (Apache-2.0),
TauCeti/Algebra/Lie/HighestWeight/CentralCharacter.lean.

Humphreys' central character chi_lambda assigns to each central element of
U(L) the scalar by which it acts on the highest-weight generator.  The
reference packages this as an algebra homomorphism only after proving the
Verma generator is nonzero and proving existence/uniqueness of the scalar.

Sweep III records the exact scalar-action relation and the graph predicate for
a proposed function.  It does not select a scalar, prove uniqueness, or bundle
the function as an algebra homomorphism.
-/

@[expose] public noncomputable section

open UniversalEnvelopingAlgebra

namespace LeanCategories.Algebra

universe u v w

variable {I : Type u} {K : Type v} {L : Type w}
variable [Finite I] [Field K] [LieRing L] [LieAlgebra K L]
variable {H : LieSubalgebra K L}

local notation "U" => UniversalEnvelopingAlgebra K L

/-- The center of the universal enveloping algebra, viewed as a K-subalgebra. -/
abbrev VermaCenterData := Subalgebra.center K U

/-- Exact relation saying that a central element acts on the canonical Verma
generator by the scalar c. -/
def IsVermaCentralCharacterValueData
    (b : LieAlgebra.Basis I H) (lam : Module.Dual K H)
    (z : VermaCenterData (K := K) (L := L)) (c : K) : Prop :=
  (z.1 : U) • vermaGeneratorData b lam =
    (algebraMap K U c) • vermaGeneratorData b lam

/-- Graph predicate for a proposed central-character function.

Once the result layer proves the scalar relation single-valued and
multiplicative/additive, this graph packages as Humphreys' algebra
homomorphism chi_lambda. -/
def IsVermaCentralCharacterData
    (b : LieAlgebra.Basis I H) (lam : Module.Dual K H)
    (chi : VermaCenterData (K := K) (L := L) → K) : Prop :=
  ∀ z, IsVermaCentralCharacterValueData b lam z (chi z)

end LeanCategories.Algebra
