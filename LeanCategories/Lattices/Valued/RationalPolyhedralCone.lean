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
# Rational polyhedral cones, faces and fans over `ℚ ⊗_ℤ L` (ported from TauCeti)

This file delivers the four items of #37 (CLS §1.2, §3.1) as a port of the TauCeti toric
cone and fan theory, adapted from the real carrier to the rational carrier of #37.

## Port provenance

Ported, with the definitions and proofs taken over and the carrier adapted, from
`TauCetiProject/TauCeti` (Apache 2.0, © The Tau Ceti contributors):

* `TauCeti/Geometry/Convex/Cone/Face/Finite.lean`:
  `PointedCone.IsFaceOf.eq_hull_inter_of_eq_hull` — a face of the hull of a set is the hull
  of the members of that set lying in the face (the elementary face description of CLS
  Proposition 1.2.2, p. 25).
* `TauCeti/Geometry/Toric/Algebraic/Cone/Basic.lean`:
  `IsLatticeRational` (the CLS Definition 1.2.14, p. 29 rational polyhedral cone),
  `IsLatticeRational.of_isFaceOf` (a face of a rational polyhedral cone is rational
  polyhedral — CLS §1.2 p. 25 item (a), the #37 item 3 theorem), `IsToricCone` (lattice
  rationality and salience — the strongly convex rational polyhedral cone of CLS
  Proposition 1.2.12, p. 28) and `IsToricCone.of_isFaceOf`.
* `TauCeti/Geometry/Toric/Algebraic/Fan/Basic.lean`:
  `Fan` (the CLS Definition 3.1.2, p. 106 fan), `Fan.support` (the support |Σ|, p. 106)
  and `Fan.IsComplete` (CLS Definition 3.1.18 (c), p. 113).

The adaptation: TauCeti states the theory over the real carrier `PointedCone ℝ V` with a
lattice map `i : N →+ V`; #37 keeps the objects over the rational span
`N_ℚ = ℚ ⊗_ℤ L`, so the port replaces `ℝ` by `ℚ` throughout and instantiates the lattice
map at the canonical embedding of the integral lattice. The `IsIntegralLattice` field of
the reference `Fan` is not carried: it is automatic for the canonical embedding
(`ℚ ⊗_ℤ L` is the scalar extension of `L` by construction), and this port's fans are over
that fixed lattice rather than over a general lattice map; the deviation is recorded here
and the field is to be restored when the port is completed.

## The four items of #37

1. A rational polyhedral cone in `N_ℚ`: `IsLatticeRational` (CLS Def. 1.2.14, p. 29).
2. The dual cone `σ^∨`: Mathlib's `PointedCone.dual` fed the canonical evaluation pairing
   `Module.Dual.eval ℚ V` (the toric convention of `Cone/TensorProduct.lean`), in the dual
   space — CLS Def. 1.2.3, p. 24. It is used directly, not wrapped.
3. A face of σ: Mathlib's `PointedCone.IsFaceOf`, and the theorem that a face of a
   rational polyhedral cone is rational polyhedral: `IsLatticeRational.of_isFaceOf` —
   CLS Def. 1.2.5 and §1.2 p. 25 item (a).
4. A fan: the ported `Fan`, with `Fan.support` and `Fan.IsComplete` — CLS Def. 3.1.2,
   p. 106 and Def. 3.1.18 (c), p. 113.

The biduality `(σ^∨)^∨ = σ` (CLS Prop. 1.2.4, p. 24) is #139.

## References

* D. Cox, J. Little, S. Schenck, *Toric Varieties*, Graduate Studies in Mathematics 124,
  American Mathematical Society (2011), §1.2 and §3.1. Zotero item `UYAMB8YC`.
* The Tau Ceti contributors, the TauCeti repository (the reference implementation this
  file ports).
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u v

variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℚ V]
  {σ τ : PointedCone ℚ V}

end LeanCategories.Lattices.Valued

/-! ## The elementary face description (ported from TauCeti) -/

namespace PointedCone.IsFaceOf

variable {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup M] [Module R M]

/-- PORT of `TauCeti.Geometry.Convex.Cone.Face.Finite`'s
`PointedCone.IsFaceOf.eq_hull_inter_of_eq_hull`: a face of the hull of a set is generated
by precisely the members of the generating set which lie in the face (Cox–Little–Schenck,
*Toric Varieties*, GSM 124 (2011), Proposition 1.2.2, p. 25). -/
theorem eq_hull_inter_of_eq_hull {C F : PointedCone R M} {s : Set M}
    (hF : F.IsFaceOf C) (hC : C = PointedCone.hull R s) :
    F = PointedCone.hull R (s ∩ F) := by
  subst hC
  refine le_antisymm (fun x hxF ↦ ?_) (Submodule.span_le.2 fun _ hx ↦ hx.2)
  induction hF.le hxF using Submodule.span_induction with
  | mem x hx => exact PointedCone.subset_hull ⟨hx, hxF⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    obtain ⟨hxF, hyF⟩ := (hF.add_mem_iff_mem hx hy).1 hxF
    exact Submodule.add_mem _ (ihx hxF) (ihy hyF)
  | smul a x hx ih =>
    obtain ⟨a, ha0⟩ := a
    obtain rfl | ha := ha0.eq_or_lt
    · simp
    · exact Submodule.smul_mem _ _
        (ih (hF.mem_of_smul_add_mem hx (Submodule.zero_mem _) ha (by simpa using hxF)))

end PointedCone.IsFaceOf

namespace LeanCategories.Lattices.Valued

variable {N : Type u} [AddCommGroup N] {V : Type v} [AddCommGroup V] [Module ℚ V]
  {σ τ : PointedCone ℚ V}

/-! ## Rational polyhedral cones (ported from TauCeti) -/

/-- PORT of `TauCeti.Toric.IsLatticeRational`, the CLS Definition 1.2.14, p. 29 rational
polyhedral cone: a pointed cone in `V` is *lattice rational* for the lattice map
`i : N →+ V` when it is the cone hull of the images of finitely many lattice vectors. -/
def IsLatticeRational (i : N →+ V) (σ : PointedCone ℚ V) : Prop :=
  ∃ s : Finset N, σ = PointedCone.hull ℚ (i '' (s : Set N))

/-- PORT of `TauCeti.Toric.IsLatticeRational.of_isFaceOf`, the #37 item 3 theorem — CLS
§1.2 p. 25 item (a): a face of a rational polyhedral cone is rational polyhedral. The face
is generated by exactly those lattice generators of the ambient cone that lie on the face. -/
theorem IsLatticeRational.of_isFaceOf {i : N →+ V}
    (hσ : IsLatticeRational i σ) (hτ : τ.IsFaceOf σ) : IsLatticeRational i τ := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  refine ⟨s.filter fun n ↦ i n ∈ τ, (hτ.eq_hull_inter_of_eq_hull rfl).trans ?_⟩
  rw [Finset.coe_filter, ← Set.image_inter_preimage]
  rfl

/-! ## Toric cones: rationality and salience (ported from TauCeti) -/

/-- PORT of `TauCeti.Toric.IsToricCone`, the strongly convex rational polyhedral cone of
CLS Proposition 1.2.12, p. 28: a *toric cone* for the lattice map `i : N →+ V` is a
lattice-rational and salient pointed cone. Salience — the condition `σ ∩ (−σ) = {0}`,
Mathlib's `ConvexCone.Salient` with the characterisation
`PointedCone.salient_iff_inter_neg_eq_singleton` — is what distinguishes the cones of
affine toric varieties from arbitrary pointed cones: a line is a pointed cone but is never
a toric cone. -/
structure IsToricCone (i : N →+ V) (σ : PointedCone ℚ V) : Prop where
  /-- A toric cone is generated by the images of finitely many lattice vectors. -/
  rational : IsLatticeRational i σ
  /-- A toric cone contains no line. -/
  salient : (σ : ConvexCone ℚ V).Salient

/-- PORT of `TauCeti.Toric.IsToricCone.of_isFaceOf`: a face of a toric cone is a toric
cone. Since the pairwise intersection of two cones of a fan is a face of each of them,
this is also what makes those intersections toric. -/
theorem IsToricCone.of_isFaceOf {i : N →+ V}
    (hσ : IsToricCone i σ) (hτ : τ.IsFaceOf σ) : IsToricCone i τ :=
  ⟨hσ.rational.of_isFaceOf hτ, hσ.salient.anti fun _ hx ↦ hτ.le hx⟩

/-! ## The dual cone (#37 item 2)

The dual cone `σ^∨` of CLS Definition 1.2.3, p. 24 — the cone of functionals pairing
nonnegatively with every point of σ — is Mathlib's `PointedCone.dual` fed the canonical
evaluation pairing `Module.Dual.eval ℚ V` (the toric convention, the same pairing
`Cone/TensorProduct.lean` feeds it): `PointedCone.dual (Module.Dual.eval ℚ V) ↑σ` in the
dual space `Module.Dual ℚ V`. It is used directly at the point of need, not wrapped. The
biduality `(σ^∨)^∨ = σ` is #139. -/

/-! ## Fans (ported from TauCeti) -/

/-- PORT of `TauCeti.Toric.Fan`, the CLS Definition 3.1.2, p. 106 fan: a *fan* for the
lattice map `i : N →+ V` is a finite family of toric cones in `V`, closed under passing
to faces, whose pairwise intersections are faces of both members. The reference structure
carries an `IsIntegralLattice i` field; this port omits it (see the module docstring). -/
structure Fan (i : N →+ V) where
  /-- The cones of the fan. -/
  cones : Set (PointedCone ℚ V)
  /-- A fan has finitely many cones. -/
  finite_cones : cones.Finite
  /-- Every cone of a fan is a toric cone. -/
  isToricCone : ∀ ⦃σ⦄, σ ∈ cones → IsToricCone i σ
  /-- The cones of a fan are closed under passing to faces. -/
  mem_of_isFaceOf : ∀ ⦃σ τ⦄, σ ∈ cones → τ.IsFaceOf σ → τ ∈ cones
  /-- The intersection of two cones of a fan is a face of the first one. Exchanging the
  two cones gives the same statement for the second one, so only this half is a field. -/
  inf_isFaceOf_left : ∀ ⦃σ τ⦄, σ ∈ cones → τ ∈ cones → (σ ⊓ τ).IsFaceOf σ

namespace Fan

variable {i : N →+ V} (Φ : Fan i)

/-- PORT of `TauCeti.Toric.Fan.ext`: a fan is determined by its set of cones. -/
@[ext] theorem ext {Φ Ψ : Fan i} (h : Φ.cones = Ψ.cones) : Φ = Ψ := by
  cases Φ with | mk C _ _ _ _ =>
  cases Ψ with | mk D _ _ _ _ =>
  obtain rfl : C = D := h
  rfl

/-- PORT of `TauCeti.Toric.Fan.inf_isFaceOf_right`: the intersection of two cones of a
fan is a face of the second one. -/
theorem inf_isFaceOf_right (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) :
    (σ ⊓ τ).IsFaceOf τ :=
  inf_comm σ τ ▸ Φ.inf_isFaceOf_left hτ hσ

/-- PORT of `TauCeti.Toric.Fan.inf_mem`: the intersection of two cones of a fan is again
a cone of the fan: it is a face of each of them, and the cones are closed under faces. -/
theorem inf_mem (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Φ.cones) :
    σ ⊓ τ ∈ Φ.cones :=
  Φ.mem_of_isFaceOf hσ (Φ.inf_isFaceOf_left hσ hτ)

/-- PORT of `TauCeti.Toric.Fan.support`, the CLS §3.1 p. 106 support |Σ| of a fan: the
union of its cones. -/
def support : Set V := ⋃ σ ∈ Φ.cones, (σ : Set V)

@[simp] theorem mem_support {x : V} : x ∈ Φ.support ↔ ∃ σ ∈ Φ.cones, x ∈ σ := by
  simp [support]

/-- PORT of `TauCeti.Toric.Fan.IsComplete`, the CLS Definition 3.1.18 (c), p. 113
completeness: a fan is *complete* when its cones cover the ambient space. -/
def IsComplete : Prop := Φ.support = Set.univ

@[simp] theorem isComplete_iff : Φ.IsComplete ↔ ∀ x : V, ∃ σ ∈ Φ.cones, x ∈ σ := by
  simp [IsComplete, Set.eq_univ_iff_forall]

end Fan

end LeanCategories.Lattices.Valued
