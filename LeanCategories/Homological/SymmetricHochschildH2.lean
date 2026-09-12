/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildComplex
public import LeanCategories.Homological.HochschildExtensions

/-!
# Symmetric Hochschild two-classes

Weibel, *An Introduction to Homological Algebra* (1994), §9.3, pp. 311--318
(FC05-C09-U028).

For commutative `R`, an `R`-bimodule is symmetric when its left and right
actions agree.  A factor set (or Hochschild two-cochain) is symmetric when it
is unchanged on swapping its two arguments.  The source denotes by `H_s²`
the submodule of `HH²` represented by symmetric two-cocycles.

The classification of commutative square-zero extensions by this submodule is
the following source row and is not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite

universe u v w

variable (k : Type u) [CommRing k]
variable (R : Type v) [CommRing R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module R M] [Module Rᵐᵒᵖ M]

/-- A bimodule over a commutative ring is symmetric when the left and right
actions agree. -/
def IsSymmetricBimodule : Prop :=
  ∀ (r : R) (m : M), r • m = (MulOpposite.op r : Rᵐᵒᵖ) • m

namespace SquareZeroExtension.FactorSet

/-- A Hochschild factor set is symmetric when `f(r,s)=f(s,r)`. -/
def IsSymmetric
    {S : SquareZeroExtension k R M}
    {σ : SquareZeroExtension.Splitting k R M S}
    (f : SquareZeroExtension.FactorSet k R M S σ) : Prop :=
  ∀ r s : R, f.map r s = f.map s r

end SquareZeroExtension.FactorSet

/-- The two arguments `(r,s)` used to evaluate a Hochschild two-cochain. -/
def hochschildPair (r s : R) : Fin 2 → R :=
  Fin.cases r (fun _ => s)

/-- Symmetry of a Hochschild two-cochain. -/
def IsSymmetricHochschildTwoCochain
    (f : HochschildCochainDegree (k := k) (R := R) (M := M) 2) : Prop :=
  ∀ r s : R,
    hochschildCochainEval (k := k) (R := R) (M := M) f (hochschildPair R r s) =
      hochschildCochainEval (k := k) (R := R) (M := M) f (hochschildPair R s r)

/-- A Hochschild cohomology class in degree two has a symmetric representative
when it is represented by a cycle whose corresponding degree-two cochain is
symmetric. -/
def HasSymmetricHochschildTwoRepresentative
    (S : HochschildCosimplicialRealization k R M)
    (x : hochschildCohomology k R M S 2) : Prop :=
  let K := AlgebraicTopology.AlternatingCofaceMapComplex.obj S.obj
  ∃ z : K.cycles 2,
    K.homologyπ 2 z = x ∧
      IsSymmetricHochschildTwoCochain k R M
        ((S.degreeIso 2).hom (K.iCycles 2 z))

/-- Definition-layer realization of Weibel's symmetric Hochschild submodule
`H_s²(R,M)`: membership is exactly representability by a symmetric two-cocycle. -/
structure SymmetricHochschildH2Realization
    (S : HochschildCosimplicialRealization k R M) where
  /-- The symmetric degree-two submodule. -/
  submodule : Submodule k (hochschildCohomology k R M S 2)
  /-- Its members are exactly the classes represented by symmetric factor sets. -/
  mem_iff : ∀ x : hochschildCohomology k R M S 2,
    x ∈ submodule ↔ HasSymmetricHochschildTwoRepresentative k R M S x

end LeanCategories.Homological
