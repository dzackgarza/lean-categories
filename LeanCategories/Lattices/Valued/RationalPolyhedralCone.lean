/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Rationalization
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Rational polyhedral cones over the rational span of an integral lattice

For an integral lattice `L`, the rational span `N_ℚ = ℚ ⊗_ℤ L` is realized here as
`TensorProduct ℤ ℚ L.obj.carrier`, with the canonical embedding `x ↦ 1 ⊗ x` of the lattice
into it (`TensorProduct.mk ℤ ℚ L.obj.carrier 1`, the `toRationalSpan` pattern of
`Rationalization.lean` with the fraction field realized as Mathlib's `ℚ`). A pointed cone in
`N_ℚ` is **rational polyhedral** when it is the conical hull of finitely many vectors of the
lattice itself: `IsRationalPolyhedral` below.

Strong convexity, `σ ∩ -σ = {0}`, is Mathlib's salience predicate on the underlying convex
cone (`ConvexCone.Salient`, with the characterisation `salient_iff_inter_neg_eq_singleton`),
and is deliberately not part of the rational-polyhedral predicate: the two conditions are
stated separately (a line through the origin is rational polyhedral but not strongly convex),
and the fan — the fourth object of #37 — asks for both together.

The biduality `(σ^∨)^∨ = σ` is not in this file: it is #139. The dual cone and the faces of
#37 follow here; the fan completes the file.

## Why the carrier is `ℚ ⊗_ℤ L` and not `RationalSpan ℤ L`

Mathlib's `PointedCone R E` demands `[PartialOrder R] [IsOrderedRing R]` on the scalar ring.
This Mathlib has no ordered-localization theory — `Algebra/Order/` carries no order instance
on `FractionRing R` for an ordered domain (probed: `PartialOrder (FractionRing ℤ)` fails to
synthesize) — while `ℚ` itself is Mathlib's canonical fraction field of `ℤ` (the instance
`Rat.isFractionRing : IsFractionRing ℤ ℚ` of `RingTheory/Localization/FractionRing.lean`),
with the full ordered-field hierarchy. The cone is therefore taken over `ℚ` in `ℚ ⊗_ℤ L`,
which is canonically isomorphic to `RationalSpan ℤ L = FractionRing ℤ ⊗_ℤ L` along
`FractionRing.algEquiv` on the left factor; the bridge is stated when the dual-cone and face
items transport the pairing across.

## References

* D. Cox, J. Little, S. Schenck, *Toric Varieties*, Graduate Studies in Mathematics 124,
  American Mathematical Society (2011), §1.2: rational polyhedral cones (Definition 1.2.14,
  p. 29) and strong convexity (Proposition 1.2.12, p. 28). Zotero item `UYAMB8YC`.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

variable (L : IntegralLatticeCat ℤ)

/-- A pointed cone σ in the rational span of an integral lattice is **rational polyhedral**
when σ is the conical hull of a finite set of vectors of the lattice `L` itself
(Cox–Little–Schenck, *Toric Varieties*, GSM 124 (2011), Definition 1.2.14, p. 29).

The cone is Mathlib's `PointedCone` over `ℚ` in `N_ℚ = ℚ ⊗_ℤ L`, i.e.
`PointedCone ℚ (TensorProduct ℤ ℚ L.obj.carrier)`; the conical hull is Mathlib's
`PointedCone.hull` — the span over nonnegative scalars; and the finiteness is encoded the way
`Submodule.FG` encodes it (`RingTheory/Finiteness/Defs.lean`): a `Finset` of generators, here
a `Finset` of `L.obj.carrier` whose image under the canonical embedding `x ↦ 1 ⊗ x` generates
the cone. Mathlib carries no rationality predicate on cones — `PointedCone` does not see the
lattice — so the restriction of the generators to the lattice is the new predicate cut over
the reused core type, the missing order on `FractionRing ℤ` having forced the scalar ring to
be `ℚ` (see the module docstring). -/
def IsRationalPolyhedral (σ : PointedCone ℚ (TensorProduct ℤ ℚ L.obj.carrier)) : Prop :=
  ∃ s : Finset L.obj.carrier,
    σ = PointedCone.hull ℚ
      ((TensorProduct.mk ℤ ℚ L.obj.carrier (1 : ℚ)) '' (s : Set L.obj.carrier))

end LeanCategories.Lattices.Valued
