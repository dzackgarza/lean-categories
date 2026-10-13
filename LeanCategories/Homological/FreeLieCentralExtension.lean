/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Extension
public import Mathlib.Algebra.Lie.Free
public import Mathlib.Algebra.Lie.IdealOperations
public import Mathlib.Algebra.Lie.Quotient

/-!
# The quotients attached to a free Lie presentation

Weibel, *An Introduction to Homological Algebra* (1994), Construction 7.9.1,
pp. 248--249 (FC05-C07-U068).

Choose a free Lie algebra `f` mapping onto `g`, and let `r` be its kernel.  Weibel
forms the relative commutator ideal `[r,f]` and the quotient map

`f/[r,f] → g`.

If `g` is perfect, Weibel then restricts this map to the image of `[f,f]`.
Centrality, surjectivity, exactness, kernel comparisons, the `H₂` identification,
and universality are proposition/result content and are deliberately not asserted
in this definition unit.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open LieAlgebra

universe u v w

variable (k : Type u) [CommRing k]

/-- The quotient map of a Lie algebra by an ideal, bundled as a Lie algebra
homomorphism. -/
def lieIdealQuotientMk {L : Type v} [LieRing L] [LieAlgebra k L]
    (I : LieIdeal k L) : L →ₗ⁅k⁆ L ⧸ I where
  toLinearMap := I.toSubmodule.mkQ
  map_lie' := by
    intro x y
    rfl

/-- A Lie homomorphism killing an ideal descends to the quotient by that ideal. -/
def lieIdealQuotientLift {L : Type v} {M : Type w}
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    (I : LieIdeal k L) (f : L →ₗ⁅k⁆ M) (hI : I ≤ f.ker) :
    L ⧸ I →ₗ⁅k⁆ M where
  toLinearMap := I.toSubmodule.liftQ f.toLinearMap <| by
    intro x hx
    exact LieHom.mem_ker.mpr (hI hx)
  map_lie' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change f ⁅x, y⁆ = ⁅f x, f y⁆
        exact f.map_lie x y

/-- A free presentation `0 → r → f → g → 0` of a Lie algebra. -/
structure FreeLiePresentation (G : Type v) [LieRing G] [LieAlgebra k G] where
  /-- Chosen free generators. -/
  Generators : Type w
  /-- The surjection from the free Lie algebra on the generators to `g`. -/
  quotientMap : FreeLieAlgebra k Generators →ₗ⁅k⁆ G
  /-- The chosen free generators generate `g`. -/
  quotientMap_surjective : Function.Surjective quotientMap

namespace FreeLiePresentation

variable {k : Type u} [CommRing k]
variable {G : Type v} [LieRing G] [LieAlgebra k G]
variable (P : FreeLiePresentation.{u, v, w} k G)

/-- The relation ideal `r=ker(f→g)`. -/
def relations : LieIdeal k (FreeLieAlgebra k P.Generators) :=
  P.quotientMap.ker

/-- The relative commutator ideal `[r,f]`. -/
def relationCommutator : LieIdeal k (FreeLieAlgebra k P.Generators) :=
  ⁅P.relations, (⊤ : LieIdeal k (FreeLieAlgebra k P.Generators))⁆

/-- The middle Lie algebra `f/[r,f]` of Construction 7.9.1. -/
abbrev centralCover :=
  FreeLieAlgebra k P.Generators ⧸ P.relationCommutator

/-- The map `f/[r,f] → g` induced by the free presentation. -/
def centralCoverProjection : P.centralCover →ₗ⁅k⁆ G :=
  lieIdealQuotientLift k P.relationCommutator P.quotientMap
    (LieSubmodule.lie_le_left _ _)

/-- The image of the relation ideal in `f/[r,f]`, representing
`r/[r,f]`. -/
def relationQuotientImage : LieIdeal k P.centralCover :=
  LieIdeal.map (lieIdealQuotientMk k P.relationCommutator) P.relations

/-- The derived ideal `[f,f]` of the chosen free Lie algebra. -/
def derivedIdeal : LieIdeal k (FreeLieAlgebra k P.Generators) :=
  ⁅(⊤ : LieIdeal k (FreeLieAlgebra k P.Generators)),
    (⊤ : LieIdeal k (FreeLieAlgebra k P.Generators))⁆

/-- The source model for `[f,f]/[r,f]`, realized as the image of `[f,f]`
inside `f/[r,f]`. -/
def perfectCover : LieIdeal k P.centralCover :=
  LieIdeal.map (lieIdealQuotientMk k P.relationCommutator) P.derivedIdeal

/-- The restriction of `f/[r,f] → g` to the perfect-cover carrier. -/
def perfectCoverProjection : P.perfectCover →ₗ⁅k⁆ G :=
  P.centralCoverProjection.comp P.perfectCover.incl

end FreeLiePresentation

end LeanCategories.Homological
