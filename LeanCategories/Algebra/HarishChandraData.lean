/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.StandardBorelData
public import LeanCategories.Algebra.VermaCentralCharacterData
public import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-!
# PBW projection and Harish--Chandra data

Definition-level realization of Humphreys FC14-C06-U048.

For a root basis with Cartan subalgebra `H`, PBW gives the vector-space
decomposition

  U(L) = U(H) + (N^- U(L) + U(L) N^+).

Rather than selecting an inverse to a triangular PBW multiplication map,
Sweep III records the exact decomposition graph.  A candidate Cartan term is
the PBW projection of `u` precisely when their difference lies in the
off-Cartan summand.  PBW proves existence and uniqueness later.

The Harish--Chandra shift is likewise recorded by its exact evaluation graph:
if `rho : H* `, then `q` is the shifted value of `h` exactly when

  eval_(lambda + rho)(q) = eval_lambda(h)

for every weight `lambda`.  In Humphreys this is the translation
`h_i |-> h_i - 1`.  The final candidate already lies in the Weyl-fixed
subalgebra.  Multiplicativity on the center, Weyl invariance, graph
totality/single-valuedness, and the central-character evaluation formula are
result-layer assertions and are not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w x

variable {I : Type u} {K : Type v} {L : Type w}
variable [Finite I] [Field K] [LieRing L] [LieAlgebra K L]
variable {H : LieSubalgebra K L}

local notation "UL" => UniversalEnvelopingAlgebra K L
local notation "UH" => UniversalEnvelopingAlgebra K H

/-- The algebra map `U(H) -> U(L)` induced by the Cartan inclusion. -/
def cartanUEAInclusionData (H : LieSubalgebra K L) :
    UniversalEnvelopingAlgebra K H →ₐ[K] UL := by
  letI : LieRing UL := LieRing.ofAssociativeRing
  exact UniversalEnvelopingAlgebra.lift K (L := H)
    ((UniversalEnvelopingAlgebra.ι K : L →ₗ⁅K⁆ UL).comp H.incl)

/-- The span of PBW terms having a negative-root factor on the left. -/
def pbwNegativeOffCartanData (b : LieAlgebra.Basis I H) : Submodule K UL :=
  Submodule.span K <| Set.range fun p : b.borelLower × UL =>
    UniversalEnvelopingAlgebra.ι K (p.1 : L) * p.2

/-- The span of PBW terms having a positive-root factor on the right. -/
def pbwPositiveOffCartanData (b : LieAlgebra.Basis I H) : Submodule K UL :=
  Submodule.span K <| Set.range fun p : UL × b.borelUpper =>
    p.1 * UniversalEnvelopingAlgebra.ι K (p.2 : L)

/-- Humphreys' off-Cartan PBW summand `N^- U(L) + U(L) N^+`. -/
def pbwOffCartanData (b : LieAlgebra.Basis I H) : Submodule K UL :=
  pbwNegativeOffCartanData b ⊔ pbwPositiveOffCartanData b

/-- Exact value graph of Humphreys' PBW projection
`xi : U(L) -> U(H)`.

The relation is total and single-valued exactly when the relevant triangular
PBW decomposition theorem is supplied. -/
def IsPBWProjectionValueData
    (b : LieAlgebra.Basis I H) (u : UL) (h : UH) : Prop :=
  u - cartanUEAInclusionData H h ∈ pbwOffCartanData b

/-- Graph predicate for a proposed PBW projection. -/
def IsPBWProjectionData
    (b : LieAlgebra.Basis I H) (xi : UL → UH) : Prop :=
  ∀ u, IsPBWProjectionValueData b u (xi u)

variable [IsLieAbelian H]

/-- Evaluation of `U(H)` at a weight.  Since `H` is abelian this is the
usual polynomial evaluation under `U(H) ≅ S(H)`. -/
def cartanUEAEvaluationData (lam : Module.Dual K H) : UH →ₐ[K] K := by
  letI : LieRing K := LieRing.ofAssociativeRing
  let f : H →ₗ⁅K⁆ K :=
    { toLinearMap := lam
      map_lie' := by
        intro x y
        calc
          lam.toFun ⁅x, y⁆ = lam.toFun 0 :=
            congrArg lam.toFun (trivial_lie_zero H H x y)
          _ = 0 := lam.map_zero
          _ = ⁅lam.toFun x, lam.toFun y⁆ := by
            simp [LieRing.of_associative_ring_bracket, mul_comm] }
  exact UniversalEnvelopingAlgebra.lift K f

/-- Exact graph of translation by `-rho` on the Cartan enveloping algebra.

The displayed equation is the source normalization characterized by
`(lambda + rho)(shift(h)) = lambda(h)`. -/
def IsCartanRhoShiftValueData
    (rho : Module.Dual K H) (h q : UH) : Prop :=
  ∀ lam : Module.Dual K H,
    cartanUEAEvaluationData (lam + rho) q =
      cartanUEAEvaluationData lam h

/-- Weyl-fixed Cartan enveloping-algebra elements for an already supplied
Weyl action.  Under `U(H) ≅ S(H)` this is Humphreys' `S(H)^W`. -/
abbrev InvariantCartanUEAData
    (W : Type x) [Monoid W] [MulSemiringAction W UH] [SMulCommClass W K UH] :=
  FixedPoints.subalgebra K UH W

/-- Exact value graph of the shifted Harish--Chandra map on the center.

The output type already enforces Weyl invariance; existence of such an output
is the result-layer invariance theorem. -/
def IsHarishChandraValueData
    {W : Type x} [Monoid W] [MulSemiringAction W UH] [SMulCommClass W K UH]
    (b : LieAlgebra.Basis I H) (rho : Module.Dual K H)
    (z : VermaCenterData (K := K) (L := L))
    (q : InvariantCartanUEAData (K := K) (H := H) W) : Prop :=
  ∃ h : UH,
    IsPBWProjectionValueData b (z : UL) h ∧
    IsCartanRhoShiftValueData rho h (q : UH)

/-- Graph predicate for a proposed Harish--Chandra function.

After the result layer proves this graph total/single-valued and proves the
algebra laws, it packages as Humphreys' algebra homomorphism
`Z(U(L)) -> S(H)^W`. -/
def IsHarishChandraData
    {W : Type x} [Monoid W] [MulSemiringAction W UH] [SMulCommClass W K UH]
    (b : LieAlgebra.Basis I H) (rho : Module.Dual K H)
    (psi : VermaCenterData (K := K) (L := L) →
      InvariantCartanUEAData (K := K) (H := H) W) : Prop :=
  ∀ z, IsHarishChandraValueData b rho z (psi z)

end LeanCategories.Algebra
