/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Relative differential sheaf data

Definition-level realization of Hartshorne FC06-C02-U265.

For a morphism `f : X ⟶ Y`, the diagonal
`Δ : X ⟶ X ×[Y] X` is an immersion.  Mathlib canonically factors an
immersion through its coborder as a closed immersion into an open subscheme.
If `I` is the ideal of that closed immersion, Hartshorne defines

`Ω_{X/Y} = Δ^*(I/I²)`.

Mathlib already supplies the diagonal immersion, its coborder factorization,
ideal sheaves, the ring-level cotangent module `Ideal.Cotangent I = I/I²`,
and pullback of sheaves of modules.  What is not packaged is the sheaf module
`I/I²`.  This file records it by affine presentation data: on each affine
open its sections are identified with the native cotangent module, compatibly
with restriction on the classes of local ideal sections.

Existence/gluing of such a module, affine comparison with Kähler
differentials, and the universal derivation are result content and are not
proved here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits

namespace LeanCategories.Schemes

universe u

variable {Z W X Y : Scheme.{u}}

/-- Affine presentations of a candidate conormal module for a morphism
`i : Z ⟶ W`: over every affine open `U ⊆ W`, its sections are identified
with `I(U)/I(U)²`, where `I = ker(i)`. -/
structure ConormalModulePresentationData
    (i : Z ⟶ W) (C : W.Modules) where
  equiv (U : W.affineOpens) :
    Γ(C, U.1) ≃ₗ[Γ(W, U.1)] (i.ker.ideal U).Cotangent

/-- Compatibility of affine conormal presentations with restriction.

It is enough to state the compatibility on classes of ideal sections: those
classes generate each native cotangent module.  The proposition records the
membership and comparison data but does not prove that such data exist. -/
def IsConormalModulePresentationData
    (i : Z ⟶ W) (C : W.Modules)
    (D : ConormalModulePresentationData i C) : Prop :=
  ∀ (U V : W.affineOpens) (j : U.1 ⟶ V.1)
      (x : i.ker.ideal V),
    ∃ hx : W.presheaf.map j.op x.1 ∈ i.ker.ideal U,
      D.equiv U
          (C.presheaf.map j.op
            ((D.equiv V).symm
              (Ideal.toCotangent (i.ker.ideal V) x))) =
        Ideal.toCotangent (i.ker.ideal U)
          ⟨W.presheaf.map j.op x.1, hx⟩

/-- Candidate carrier for a conormal sheaf.  Keeping the carrier separate from
its specification makes the ambient type nonempty without proving the conormal
sheaf gluing theorem. -/
structure ConormalModuleCandidateData (W : Scheme.{u}) where
  module : W.Modules

instance (W : Scheme.{u}) : Nonempty (ConormalModuleCandidateData W) :=
  ⟨⟨SheafOfModules.unit W.ringCatSheaf⟩⟩

/-- A candidate module is the conormal module of a closed immersion when it has
affine `I/I²` presentations compatible with restriction. -/
def IsConormalModuleData
    (i : Z ⟶ W) [IsClosedImmersion i]
    (C : ConormalModuleCandidateData W) : Prop :=
  ∃ D : ConormalModulePresentationData i C.module,
    IsConormalModulePresentationData i C.module D

/-- The conormal-module datum `I/I²` selected by its affine specification.
Existence of a candidate satisfying the specification is a Sweep-IV theorem. -/
def conormalModuleData
    (i : Z ⟶ W) [IsClosedImmersion i] : W.Modules :=
  (Classical.epsilon (IsConormalModuleData i)).module

/-- The canonical open subscheme of `X ×[Y] X` in which the diagonal is a
closed immersion. -/
abbrev relativeDifferentialsCoborder (f : X ⟶ Y) :=
  (pullback.diagonal f).coborderRange

/-- The diagonal regarded as a closed immersion into its canonical coborder. -/
def relativeDifferentialsDiagonalLift (f : X ⟶ Y) :
    X ⟶ (relativeDifferentialsCoborder f).toScheme :=
  (pullback.diagonal f).liftCoborder

/-- The conormal module `I/I²` of the diagonal inside its coborder. -/
def relativeDifferentialsConormalData (f : X ⟶ Y) :
    (relativeDifferentialsCoborder f).toScheme.Modules :=
  conormalModuleData (pullback.diagonal f).liftCoborder

/-- Hartshorne's relative differential sheaf datum
`Ω_{X/Y} = Δ^*(I/I²)`. -/
def relativeDifferentialsData (f : X ⟶ Y) : X.Modules :=
  (Scheme.Modules.pullback (pullback.diagonal f).liftCoborder).obj
    (relativeDifferentialsConormalData f)

end LeanCategories.Schemes
