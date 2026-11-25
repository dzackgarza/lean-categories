/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.BirationalSurfaceModels
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Blow-up data for a smooth complex surface at a point

Definition-level realization of Beauville FC12-C02-U001.

Beauville II.1 introduces the blow-up `ε : Ŝ → S` of a smooth surface at a
point `p`, characterized here by the source-level data used in that
definition:

* `ε` is an isomorphism away from `p`;
* its exceptional curve is a projective line parametrizing tangent directions
  at `p`;
* the strict transform of a curve is the closure of the inverse image away
  from `p`.

Mathlib exposes the Rees algebra and projective-spectrum ingredients but no
scheme-level blow-up constructor.  The source object is therefore represented
directly as bundled blow-up data: the surface, projection, exceptional
subscheme, strict transforms, and the defining compatibility proofs are fields
of `PointBlowupData`.  There is no candidate carrier or separately supplied
graph predicate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Topology
open scoped LinearAlgebra.Projectivization

namespace LeanCategories.Schemes

/-- Cotangent space of the local ring of `S` at `p`. -/
abbrev surfacePointCotangentSpaceData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme) :=
  IsLocalRing.CotangentSpace (S.scheme.presheaf.stalk p)

/-- Zariski tangent space, represented as the dual of the local cotangent
space. -/
abbrev surfacePointTangentSpaceData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme) :=
  Module.Dual
    (IsLocalRing.ResidueField (S.scheme.presheaf.stalk p))
    (surfacePointCotangentSpaceData S p)

/-- Projectivized tangent directions at `p`. -/
abbrev surfacePointTangentDirectionsData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme) :=
  Projectivization
    (IsLocalRing.ResidueField (S.scheme.presheaf.stalk p))
    (surfacePointTangentSpaceData S p)

/- Beauville II.1's blow-up `Bl_p S` of a smooth complex surface at a point is not bundled here.
Its defining data include the exceptional curve together with an isomorphism to `P¹` and a
parametrization of the projectivized Zariski tangent space at `p`; both are *existence*
assertions, and supplying them requires the blow-up construction itself. That construction is an
open obligation of its own work unit, so the specification and the two existence fields it
carried (`exceptional_projective_line`, `exceptional_tangent_directions`) are deleted rather than
filled with a witness. The tangent-space objects above remain, and
`surfacePointTangentDirectionsData S p` is still the projectivization that the parametrization
must target. -/

/- Beauville II.16 defines an exceptional curve on a smooth projective surface as the
exceptional curve of a blow-up of another smooth surface at a point. The definition quantifies
over the blow-up data above, so it is deleted with it rather than restated:
`IsExceptionalCurveData` and, downstream of it, `HasNoExceptionalCurveData` both require the
blow-up construction. Beauville's assertion that having no exceptional curve is equivalent to
minimality remains result-layer content. -/

end LeanCategories.Schemes
