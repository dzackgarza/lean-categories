/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Topology.Sheaves.Limits

/-!
# Formal-completion data

Definition-level realization of Hartshorne FC06-C02-U310.

For a noetherian scheme `X` and a closed subscheme cut out by an ideal
sheaf `I`, the formal completion has underlying topological space
`Supp(I)` and structure sheaf

`lim_n O_X / I^(n+1)`.

The current Mathlib pin supplies ideal-sheaf powers and associated closed
subschemes, quotient rings on affine opens, sheaf limits, and locally ringed
spaces, but no packaged formal-completion object.  This file therefore records
the quotient tower by its affine section rings and canonical quotient
transition maps, and specifies a locally ringed-space candidate whose
structure sheaf is the inverse limit of that tower.

Existence of a candidate satisfying the specification, independence from the
chosen defining ideal, and affine identification with adic completion are
result content and are not proved here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits

namespace LeanCategories.Schemes

universe u

variable {X : Scheme.{u}}

/-- The open of the closed support corresponding to an open of the ambient
scheme. -/
abbrev formalCompletionSupportOpen
    (I : X.IdealSheafData) (U : X.Opens) : I.subscheme.Opens :=
  I.subschemeι ⁻¹ᵁ U

/-- Presentation data for an inverse system intended to be
`(O_X / I^(n+1))_n` on the fixed closed support of `I`.

Only affine section identifications are stored as data.  Compatibility of the
tower maps with the canonical quotient maps is a separate proposition below.
-/
structure FormalCompletionTowerPresentationData
    (I : X.IdealSheafData)
    (T : ℕᵒᵖ ⥤ I.subscheme.carrier.Sheaf CommRingCat) where
  sectionIso (n : ℕ) (U : X.affineOpens) :
    ((T.obj (op n)).obj.obj
      (op (formalCompletionSupportOpen I U.1))) ≅
      CommRingCat.of (Γ(X, U.1) ⧸ (I.ideal U) ^ (n + 1))

/-- The affine presentations of the quotient tower use the canonical maps
`A/I^(n+2) → A/I^(n+1)` on every affine open. -/
def IsFormalCompletionTowerPresentationData
    (I : X.IdealSheafData)
    (T : ℕᵒᵖ ⥤ I.subscheme.carrier.Sheaf CommRingCat)
    (D : FormalCompletionTowerPresentationData I T) : Prop :=
  ∀ (n : ℕ) (U : X.affineOpens),
    (D.sectionIso (n + 1) U).inv ≫
        (T.map (homOfLE (Nat.le_succ n)).op).1.app
          (op (formalCompletionSupportOpen I U.1)) ≫
        (D.sectionIso n U).hom =
      CommRingCat.ofHom
        (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := I.ideal U)
            (Nat.le_succ (n + 1))))

/-- Candidate data for the formal completion.  The carrier equality records
that the underlying topological space is exactly the closed support, while the
quotient tower is kept on that fixed support.

The ambient candidate type is nonempty independently of the formal-completion
existence theorem. -/
structure FormalCompletionCandidateData (I : X.IdealSheafData) where
  space : LocallyRingedSpace.{u}
  carrierEq : space.carrier = I.subscheme.carrier
  quotientTower : ℕᵒᵖ ⥤ I.subscheme.carrier.Sheaf CommRingCat

instance (I : X.IdealSheafData) :
    Nonempty (FormalCompletionCandidateData I) :=
  ⟨⟨I.subscheme.toLocallyRingedSpace, rfl,
    (Functor.const ℕᵒᵖ).obj I.subscheme.sheaf⟩⟩

/-- The candidate structure sheaf transported along its recorded equality of
carriers to the fixed closed support. -/
def FormalCompletionCandidateData.sheafOnSupport
    {I : X.IdealSheafData} (P : FormalCompletionCandidateData I) :
    I.subscheme.carrier.Sheaf CommRingCat :=
  P.carrierEq ▸ P.space.sheaf

/-- Hartshorne's formal-completion specification:
the carrier is the closed support and the structure sheaf is the inverse limit
of the canonically presented quotient tower `O_X/I^(n+1)`. -/
def IsFormalCompletionData
    [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)
    (P : FormalCompletionCandidateData I) : Prop :=
  ∃ D : FormalCompletionTowerPresentationData I P.quotientTower,
    IsFormalCompletionTowerPresentationData I P.quotientTower D ∧
      Nonempty
        (P.sheafOnSupport ≅ limit P.quotientTower)

end LeanCategories.Schemes
