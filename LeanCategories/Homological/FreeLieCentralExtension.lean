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
# The central extension attached to a free Lie presentation

Weibel, *An Introduction to Homological Algebra* (1994), Construction 7.9.1,
pp. 248--249 (FC05-C07-U068).

Choose a free Lie algebra `f` mapping onto `g`, and let `r` be its kernel.  Weibel
forms the relative commutator ideal `[r,f]` and the central extension

`0 → r/[r,f] → f/[r,f] → g → 0`.

If `g` is perfect, Weibel then restricts to `[f,f]/[r,f]` and proves that this
restriction is the universal central extension with kernel `H₂(g,k)`.  Those
surjectivity, kernel-identification, and universality assertions are theorem-layer
content and are deliberately not asserted here.
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

@[simp]
lemma lieIdealQuotientLift_mk {L : Type v} {M : Type w}
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    (I : LieIdeal k L) (f : L →ₗ⁅k⁆ M) (hI : I ≤ f.ker) (x : L) :
    lieIdealQuotientLift k I f hI (LieSubmodule.Quotient.mk x) = f x :=
  rfl

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

/-- `[r,f]` is contained in `r`, so the presentation map kills it. -/
lemma relationCommutator_le_ker : P.relationCommutator ≤ P.quotientMap.ker := by
  exact LieSubmodule.lie_le_left _ _

/-- The middle Lie algebra `f/[r,f]` of Construction 7.9.1. -/
abbrev centralCover :=
  FreeLieAlgebra k P.Generators ⧸ P.relationCommutator

/-- The map `f/[r,f] → g` induced by the free presentation. -/
def centralCoverProjection : P.centralCover →ₗ⁅k⁆ G :=
  lieIdealQuotientLift k P.relationCommutator P.quotientMap
    P.relationCommutator_le_ker

lemma centralCoverProjection_surjective :
    Function.Surjective P.centralCoverProjection := by
  intro g
  obtain ⟨f, rfl⟩ := P.quotientMap_surjective g
  exact ⟨LieSubmodule.Quotient.mk f, rfl⟩

/-- The Lie-algebra extension determined by the surjection
`f/[r,f] → g`.  Its kernel is canonically the image of `r`, i.e. the source
model for `r/[r,f]`. -/
def centralExtension :
    LieAlgebra.Extension k P.centralCoverProjection.ker G :=
  (LieAlgebra.isExtension_of_surjective
    P.centralCoverProjection P.centralCoverProjection_surjective).extension

/-- The image of the relation ideal in `f/[r,f]`, representing
`r/[r,f]`. -/
def relationQuotientImage : LieIdeal k P.centralCover :=
  LieIdeal.map (lieIdealQuotientMk k P.relationCommutator) P.relations

/-- Definition-layer realization that Weibel's quotient extension is central
and that its kernel is exactly the image of the relation ideal. -/
structure CentralExtensionRealization : Prop where
  /-- `ker(f/[r,f]→g)=r/[r,f]`. -/
  kernel_eq_relationQuotient :
    P.centralCoverProjection.ker = P.relationQuotientImage
  /-- The kernel lies in the center of `f/[r,f]`. -/
  central : P.centralCoverProjection.ker ≤ LieAlgebra.center k P.centralCover

end FreeLiePresentation

end LeanCategories.Homological
