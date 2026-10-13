/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.VermaModuleData
public import Mathlib.Algebra.Module.RingHom

/-!
# Verma annihilator data

Definition-level realization of Humphreys FC14-C06-U022, adapted from the
Verma universal-property construction in TauCetiProject/TauCeti at
0ce0e8862fb5aeb94a921ab5dc54e2fce17c2d0b (Apache-2.0).

For a vector `v` in an `L`-module `V`, the universal enveloping algebra acts
through its canonical representation `U(L) -> End_K(V)`. The left ideal of
elements annihilating `v` is therefore literally the kernel of the
`U(L)`-linear map `u |-> u • v`.

Humphreys' `J(lambda)` is this construction specialized to a maximal vector
`v+` in the previously constructed irreducible highest-weight module
`V(lambda)`. The induced map `Z(lambda) = U(L)/I(lambda) -> V(lambda)` needs
only the displayed containment `I(lambda) <= J(lambda)`. This file records
that quotient construction parametrically; existence and the highest-weight
properties of `V(lambda)` are result-layer content and are not reproved here.
-/

@[expose] public noncomputable section

open UniversalEnvelopingAlgebra

namespace LeanCategories.Algebra

universe u v w x

variable {I : Type u} {K : Type v} {L : Type w} {V : Type x}
variable [Finite I] [Field K] [LieRing L] [LieAlgebra K L]
variable {H : LieSubalgebra K L}
variable [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

local notation "U" => UniversalEnvelopingAlgebra K L

/-- The canonical representation of `U(L)` on an `L`-module. -/
def ueaRepresentationData : U →ₐ[K] Module.End K V :=
  UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V)

/-- The `U(L)`-module structure induced by the canonical representation. -/
abbrev ueaModuleData : Module U V :=
  Module.compHom V (ueaRepresentationData (K := K) (L := L) (V := V)).toRingHom

/-- The left ideal of `U(L)` annihilating a vector `v`.

The `U(L)`-module structure on `V` is restriction of scalars along the
canonical representation. Hence this is exactly
`{u : U(L) | u • v = 0}`, with left-ideal closure supplied by the kernel. -/
def ueaVectorAnnihilatorData (v : V) : Ideal U :=
  letI : Module U V := ueaModuleData (K := K) (L := L) (V := V)
  LinearMap.ker (LinearMap.toSpanSingleton U V v)

/-- The exact descent condition in Humphreys' construction:
`I(lambda)` is contained in the annihilator of the chosen maximal vector.

For the source specialization this follows from the defining highest-weight
relations of the maximal vector; that result is intentionally not bundled
into the Sweep-III construction. -/
def IsVermaAnnihilatorData
    (b : LieAlgebra.Basis I H) (lam : Module.Dual K H) (v : V) : Prop :=
  vermaIdealData b lam ≤ ueaVectorAnnihilatorData (K := K) (L := L) v

/-- The quotient map `Z(lambda) -> V` induced by
`I(lambda) <= Ann(v)`.

Specializing `V` and `v` to Humphreys' `V(lambda)` and its maximal vector
gives the canonical map displayed in FC14-C06-U022. -/
def vermaAnnihilatorQuotientMapData
    (b : LieAlgebra.Basis I H) (lam : Module.Dual K H) (v : V)
    (h : IsVermaAnnihilatorData b lam v) :
    letI : Module U V := ueaModuleData (K := K) (L := L) (V := V)
    VermaModuleData b lam →ₗ[U] V := by
  letI : Module U V := ueaModuleData (K := K) (L := L) (V := V)
  apply Submodule.liftQ (vermaIdealData b lam) (LinearMap.toSpanSingleton U V v)
  simpa only [IsVermaAnnihilatorData, ueaVectorAnnihilatorData] using h

end LeanCategories.Algebra
