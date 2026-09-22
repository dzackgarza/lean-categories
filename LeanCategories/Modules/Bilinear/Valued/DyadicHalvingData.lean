/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Torsion
public import LeanCategories.Modules.FractionRingQuotient
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.LinearAlgebra.Pi

/-!
# Dyadic halving presentation data

Peters--Sterk FC11-C09-U022 (Definition 9.3.10).

The source chooses a cyclic decomposition of a finite `2`-primary group,
raises every cyclic order from `2^k` to `2^(k+1)`, and prescribes the new
pairing on the corresponding generators by the notation `1/2 b`.

Sweep III records exactly that presentation data.  In particular, it does
not choose halves in `ℚ/ℤ`, prove that compatible choices exist, extend the
generator values to a bilinear form, prove symmetry, or prove any
well-definedness/isometry statement.  Those are proposition-level
obligations for Sweep IV.
-/

@[expose] public noncomputable section

namespace LeanCategories.Modules.Bilinear.Valued

universe u

open LeanCategories.Modules
open Sym2

abbrev RationalQuotientValue :=
  LeanCategories.Modules.RationalQuotientIntegers

/-- A finite cyclic `2`-primary presentation with one positive exponent for
each chosen cyclic generator.  The source carrier has factors `ℤ/2^kℤ`. -/
abbrev dyadicCyclicPresentationCarrierData {n : ℕ}
    (exponent : Fin n → ℕ+) :=
  (i : Fin n) → ZMod (2 ^ (exponent i : ℕ))

/-- The order-raised carrier in Peters--Sterk's halving construction: each
factor `ℤ/2^kℤ` is replaced by `ℤ/2^(k+1)ℤ`. -/
abbrev dyadicHalvingCarrierData {n : ℕ}
    (exponent : Fin n → ℕ+) :=
  (i : Fin n) → ZMod (2 ^ ((exponent i : ℕ) + 1))

/-- The chosen cyclic decomposition of the source `2`-primary torsion group.

The equivalence is data supplied by the source's phrase "in a chosen
decomposition"; Sweep III does not prove existence of such a decomposition. -/
structure DyadicHalvingPresentationData
    (A : FiniteTorsionSymBilinModuleCat ℤ RationalQuotientValue) where
  rank : ℕ
  exponent : Fin rank → ℕ+
  sourceEquiv :
    dyadicCyclicPresentationCarrierData exponent ≃ₗ[ℤ] A.obj.carrier

namespace DyadicHalvingPresentationData

variable {A : FiniteTorsionSymBilinModuleCat ℤ RationalQuotientValue}

/-- The distinguished source generator `e_i` determined by the chosen cyclic
presentation. -/
def sourceGenerator (D : DyadicHalvingPresentationData A)
    (i : Fin D.rank) : A.obj.carrier :=
  D.sourceEquiv (Pi.single i 1)

/-- The distinguished generator `𝐞_i` in the order-raised halving carrier. -/
def halvedGenerator (D : DyadicHalvingPresentationData A)
    (i : Fin D.rank) : dyadicHalvingCarrierData D.exponent :=
  Pi.single i 1

/-- Symmetric generator-pairing values for the order-raised carrier.

Indexing by unordered pairs makes symmetry part of the data rather than a
proof obligation.  This is deliberately only generator data; extending it to
a bilinear form is not part of Sweep III. -/
abbrev GeneratorPairingData (D : DyadicHalvingPresentationData A) :=
  Sym2 (Fin D.rank) → RationalQuotientValue

/-- The source equation `𝐛(𝐞_i,𝐞_j) = (1/2)b(e_i,e_j)`, expressed without
choosing a division-by-two operation on `ℚ/ℤ`: doubling the supplied new value
must recover the original generator pairing.

This predicate records the defining equation only.  Existence of such values
and extension to a symmetric bilinear form are result-layer obligations. -/
def IsGeneratorPairingHalving
    (D : DyadicHalvingPresentationData A)
    (B : GeneratorPairingData D) : Prop :=
  ∀ i j, (2 : ℤ) • B s(i, j) =
    A.obj.pairing (D.sourceGenerator i) (D.sourceGenerator j)

end DyadicHalvingPresentationData

end LeanCategories.Modules.Bilinear.Valued
