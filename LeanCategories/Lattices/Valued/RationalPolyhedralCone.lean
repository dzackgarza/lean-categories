/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Rationalization
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Face.Basic

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

namespace LeanCategories.Lattices.Valued

variable (L : IntegralLatticeCat ℤ)

/-! ## The dual cone -/

/-- The **dual cone** of a pointed cone σ in the rational span `N_ℚ = ℚ ⊗_ℤ L`, in the dual
space `Module.Dual ℚ N_ℚ`, with respect to the canonical evaluation pairing
(Cox–Little–Schenck, *Toric Varieties*, GSM 124 (2011), Definition 1.2.3, p. 24:
σ^∨ = {m ∈ M | ⟨m, x⟩ ≥ 0 for all x ∈ σ}).

The dual is Mathlib's `PointedCone.dual` fed the canonical evaluation pairing
`Module.Dual.eval ℚ N_ℚ` (the toric convention, the same pairing `Cone/TensorProduct.lean`
feeds it): the carrier is the set of functionals pairing nonnegatively with every point of σ.
The dual cone of a rational polyhedral cone is rational polyhedral in the dual lattice
(Cox–Little–Schenck, §1.2, noted after Definition 1.2.14); that statement needs the dual
lattice, which the evaluation pairing does not carry, so it is not asserted here. -/
def rationalDual (σ : PointedCone ℚ (TensorProduct ℤ ℚ L.obj.carrier)) :
    PointedCone ℚ (Module.Dual ℚ (TensorProduct ℤ ℚ L.obj.carrier)) :=
  PointedCone.dual (Module.Dual.eval ℚ (TensorProduct ℤ ℚ L.obj.carrier)) ↑σ

/-! ## Strong convexity -/

/-- A pointed cone σ in the rational span is **strongly convex** when σ ∩ (−σ) = {0}
(Cox–Little–Schenck, *Toric Varieties*, GSM 124 (2011), Proposition 1.2.12, p. 28, where
this is listed among the equivalent conditions).

The predicate is Mathlib's salience of the underlying convex cone
(`ConvexCone.Salient`), with the intersection-with-negative characterisation
`PointedCone.salient_iff_inter_neg_eq_singleton`; it is deliberately not part of
`IsRationalPolyhedral` — a line through the origin is rational polyhedral but not strongly
convex — and the fan (#37 item 4) asks for both together. -/
def IsStronglyConvex (σ : PointedCone ℚ (TensorProduct ℤ ℚ L.obj.carrier)) : Prop :=
  (σ : ConvexCone ℚ (TensorProduct ℤ ℚ L.obj.carrier)).Salient

/-! ## Faces

The **face relation** of #37 item 3 is Mathlib's `PointedCone.IsFaceOf`
(`Geometry/Convex/Cone/Face/Basic.lean`), the intrinsic extremal relation between pointed
cones: `τ.IsFaceOf σ` when τ is a subcone of σ and any point of σ a positive multiple of
which translates into τ already lies in τ. The theorem that a face of a rational polyhedral
cone is rational polyhedral (Cox–Little–Schenck, *Toric Varieties*, GSM 124 (2011), §1.2
p. 25, item (a)) is the finiteness statement that the fan's face-closure condition
preserves: the generators of the face are the generators of the whole cone that the face
contains, extracted from the conical-combination decomposition of a face point through the
face-sum lemma `IsFaceOf.mem_of_sum_smul_mem` of Mathlib's face API. -/

/-! ## Fans -/

/-- A **fan** in the rational span of an integral lattice: a finite collection of strongly
convex rational polyhedral cones, closed under taking faces, in which any two cones meet in
a face of each (Cox–Little–Schenck, *Toric Varieties*, GSM 124 (2011), Definition 3.1.2,
p. 106). -/
def IsFan (F : Set (PointedCone ℚ (TensorProduct ℤ ℚ L.obj.carrier))) : Prop :=
  F.Finite ∧
  (∀ σ ∈ F, IsStronglyConvex L σ ∧ IsRationalPolyhedral L σ) ∧
  (∀ σ ∈ F, ∀ τ, τ.IsFaceOf σ → τ ∈ F) ∧
  (∀ σ ∈ F, ∀ σ' ∈ F, (σ ⊓ σ').IsFaceOf σ ∧ (σ ⊓ σ').IsFaceOf σ')

/-- The **support** of a fan: the union of its cones, |Σ| = ⋃ σ
(Cox–Little–Schenck, *Toric Varieties*, GSM 124 (2011), §3.1, p. 106). -/
def fanSupport (F : Set (PointedCone ℚ (TensorProduct ℤ ℚ L.obj.carrier))) :
    Set (TensorProduct ℤ ℚ L.obj.carrier) :=
  ⋃ σ ∈ F, (σ : Set (TensorProduct ℤ ℚ L.obj.carrier))

/-- A fan is **complete** when its support is the whole space
(Cox–Little–Schenck, *Toric Varieties*, GSM 124 (2011), Definition 3.1.18 (c), p. 113,
stated there as |Σ| = N_ℝ; over the rational span of #37 the whole rational space,
the scalar extension to ℝ being the real form of #37's later items). -/
def IsFanComplete (F : Set (PointedCone ℚ (TensorProduct ℤ ℚ L.obj.carrier))) : Prop :=
  fanSupport L F = Set.univ

end LeanCategories.Lattices.Valued
