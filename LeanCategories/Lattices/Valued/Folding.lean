/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.VinbergE10Chamber
public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import LeanCategories.Lattices.Valued.Sublattice

/-!
# Folding a Lorentzian chamber along an involution (`#116`)

For an even lattice `M` of signature `(1, n)` with a chamber `C(R)` of `W(M)` (`#23`,
`WeylChambers.lean`) and an involutive isometry `σ` of `M`, this file defines the **fixed
sublattice** `M^σ`, the **folded vector** of a lattice vector, the **folded root set** and its
**Coxeter diagram**, and proves the **folding theorem**: inside the invariant part of the real
form, the folded roots cut out exactly the trace of the chamber `C(R)`.

The direction of the construction is the source's: **invariants**, not coinvariants. Alexeev,
Engel, Garza and Schaffler, *Compact moduli of Enriques surfaces of degree 2*, Nagoya Math. J. 259
(2025), arXiv:2312.03638v2, §3.7:

* Definition 3.3 (printed p. 11): for a lattice `Λ` with an involution `I` and `α ∈ Λ`, the
  folded vector is `α^I = α` if `I α = α` and `α^I = α + I α` otherwise. It is a vector of
  `Λ^{I=1}`, the *fixed* (invariant) sublattice — `foldedVector_mem_fixed` — and it depends only
  on the `I`-orbit of `α` (`foldedVector_invariant`), which is what makes the folded diagram
  smaller than the diagram it comes from.
* Lemma 3.4 (printed pp. 11–12): for the involution `I = -I_En` on `T_dP`, a root `α` of `T_dP`
  with `α_I² < 0` folds to a root of the invariant lattice `T_dP^{I=1} = T_En`. The arithmetic of
  its proof is the identity `α_I² = 2 α² + 2 α · I α` (`pairing_folded_self_of_not_fixed`,
  `pairing_folded_self_of_fixed`), and it is the case analysis of `pairing_folded_self_of_not_fixed`
  that decides which roots survive the folding.
* Definition 3.7 (printed p. 12): the folded diagram `G^J` has the vertices `α^J` for the roots
  `α` of `G` for which `α^J` is again a root of `Λ^{J=1}` (`foldedRootFamily`,
  `foldedCoxeterDiagram`).
* Lemma 3.8 (printed p. 12): "Let `C` be a chamber for the action of `W(Γ_dP,e)` on the positive
  cone `C(T_dP)` whose intersection with `T_En` has maximal dimension. Then `C^J := C ∩ T_En ⊗ R`
  is a fundamental chamber for `W(Γ_{En,2,e})` and its Coxeter diagram is the folded diagram."
  The proof is two lines and is exactly what is formalized here: "the intersection of the
  positive cone `C(T_En)` with `α^⊥` is the same as with `α_J^⊥`". That is
  `mem_weylChamberCone_folded_iff` and `mem_rootInteriorCone_folded_iff` — the folded roots cut
  out, in the invariant part of the real form, the trace of the cone cut out by `R` — and
  `chamberOf_folded_trace`, which identifies that trace with the chamber of any of its points by
  `IsChamberWithWalls.chamberOf_eq` (`#23`).

## What is *not* here, and why

`IsChamberWithWalls M^σ ...` as a statement about the invariant lattice *as an object of the
category* needs the root system of `M^σ` itself: the fields `roots_mem` (every folded root is a
reflective root of `M^σ` of negative square) and `interior_regular` (the folded interior cone
meets no mirror of a negative reflective root of `M^σ`) are not consequences of folding. In the
source they are Lemma 3.4's converse — "Vice versa, all roots of `T_En` are of these three
types" — proved there by the classification of `(-2)`- and `(-4)`-vectors in `T_En` up to
`Γ_En`. Folding alone gives the wall correspondence proved below; without a root computation for
the invariant lattice the predicate cannot be discharged, so it is not stated vacuously here.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces with a
  numerical polarization of degree 2*, Nagoya Math. J. 259 (2025), arXiv:2312.03638v2, §3.7
  (Definition 3.3, Lemmas 3.4, 3.8, Definition 3.7, printed pp. 11–12).
* E. B. Vinberg, *The groups of unit elements of certain quadratic forms*, Mat. Sb. 87 (1972), §1.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1, for chambers and their walls.

## LC-09 record

Searched (this repository, and the Mathlib source at `/opt/mathlib` at the pinned head) for a
folding construction, an invariant-sublattice construction and a folded Coxeter diagram before
writing any declaration: `rg -n -i "fold|involution"` over `LeanCategories/` (hits:
`Sublattice.lean`'s `IsPrimitiveSubmodule`/`saturation`, `Gluing/Overlattice*`'s involutions of
glued lattices, and `LocalHomologyCoveringData`-style `Data` files with no relation to folding; no
folded vector, no folded diagram, no invariant sublattice of an isometry exists in the
repository); `rg "realFormOrthogonalHom|orthogonalGroupBaseChangeHom"` (the scalar-extension
homomorphism `LatticeCone.realFormOrthogonalHom`, used for the invariant part of the real form);
`rg "foldedVector|foldedRootSet|foldedCoxeterDiagram"` (no hits in this repository or Mathlib);
`rg "formedSublattice|orthogonalSubmodule"` (`Sublattice.formedSublattice` is the existing
submodule-with-restricted-form constructor, reused for the invariant sublattice);
Mathlib `rg "IsReflective|CoxeterMatrix|IsCoxeter"` (the combinatorial `CoxeterMatrix` at
`Mathlib/GroupTheory/Coxeter/Matrix.lean:69`, which carries no geometric chamber, and
`LinearMap.IsReflective`, already the base of `RootSystem.IsReflectiveRoot`). Nothing in
Mathlib or in the corpus supplies a folding of a reflection-group chamber along an involution,
so nothing is ported and the statements below are proved directly from the pairing.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Algebra
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-! ## The invariant part of an involution -/

/-- The action of an isometry on the carrier, as a `ℤ`-linear map. -/
noncomputable def isometryLinearMap (g : OrthogonalGroup L.obj) :
    L.obj.obj.carrier →ₗ[ℤ] L.obj.obj.carrier :=
  (g.1 : L.obj.obj.carrier ≃ₗ[ℤ] L.obj.obj.carrier).toLinearMap

@[simp] theorem isometryLinearMap_apply (g : OrthogonalGroup L.obj)
    (x : L.obj.obj.carrier) : isometryLinearMap g x = g.1 x := rfl

/-- **The fixed sublattice** `M^σ`: the invariant part of the lattice under an involution. It is
the kernel of `σ - 1`, hence saturated: `M^σ` contains no vector whose nonzero multiple it
contains. -/
noncomputable def involutionFixedSubmodule (g : OrthogonalGroup L.obj) :
    Submodule ℤ L.obj.obj.carrier :=
  LinearMap.ker (isometryLinearMap g - 1)

theorem mem_involutionFixedSubmodule_iff (g : OrthogonalGroup L.obj)
    {x : L.obj.obj.carrier} : x ∈ involutionFixedSubmodule g ↔ g.1 x = x := by
  rw [involutionFixedSubmodule, LinearMap.mem_ker]
  change isometryLinearMap g x - x = 0 ↔ g.1 x = x
  rw [isometryLinearMap_apply, sub_eq_zero]

/-- **The folded vector** (AEGS Definition 3.3): `α^I = α` if `α` is fixed by the involution and
`α^I = α + I α` otherwise. -/
noncomputable def foldedVector (g : OrthogonalGroup L.obj) (x : L.obj.obj.carrier) :
    L.obj.obj.carrier := by
  classical
  exact if g.1 x = x then x else x + g.1 x

theorem foldedVector_of_fixed (g : OrthogonalGroup L.obj) {x : L.obj.obj.carrier}
    (hx : g.1 x = x) : foldedVector g x = x := by
  classical exact ite_eq_left hx

theorem foldedVector_of_not_fixed (g : OrthogonalGroup L.obj) {x : L.obj.obj.carrier}
    (hx : g.1 x ≠ x) : foldedVector g x = x + g.1 x := by
  classical exact ite_eq_right hx

/-- An involution of the lattice is an involution of its carrier. -/
theorem isometry_apply_apply (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (x : L.obj.obj.carrier) : g.1 (g.1 x) = x := by
  have hh : (g.1 : L.obj.obj.carrier ≃ₗ[ℤ] L.obj.obj.carrier) * g.1 = 1 := by
    simpa using congrArg (fun e : OrthogonalGroup L.obj =>
      (e.1 : L.obj.obj.carrier ≃ₗ[ℤ] L.obj.obj.carrier)) hg
  calc g.1 (g.1 x) = (g.1 * g.1) x := rfl
    _ = (1 : L.obj.obj.carrier ≃ₗ[ℤ] L.obj.obj.carrier) x := by rw [hh]
    _ = x := rfl

/-- **`α^I` lies in the invariant sublattice** (AEGS Definition 3.3, "we call the following
vector `α^I ∈ Λ^{I=1}`"). -/
theorem foldedVector_mem_fixed (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (x : L.obj.obj.carrier) : foldedVector g x ∈ involutionFixedSubmodule g := by
  rw [mem_involutionFixedSubmodule_iff]
  by_cases hx : g.1 x = x
  · rw [foldedVector_of_fixed g hx]; exact hx
  · rw [foldedVector_of_not_fixed g hx, map_add, isometry_apply_apply g hg, add_comm]

/-- The folded vector depends only on the orbit of the involution: this is what makes the folded
diagram's vertex set the set of orbits. -/
theorem foldedVector_invariant (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (x : L.obj.obj.carrier) : foldedVector g (g.1 x) = foldedVector g x := by
  by_cases hx : g.1 x = x
  · rw [hx, foldedVector_of_fixed g hx]
  · have hx' : g.1 (g.1 x) ≠ g.1 x := by
      rw [isometry_apply_apply g hg]
      exact fun h => hx h.symm
    rw [foldedVector_of_not_fixed g hx', foldedVector_of_not_fixed g hx,
      isometry_apply_apply g hg, add_comm]

/-! ## Pairings with the folded vector

The three cases of AEGS Definition 3.3, each a two-line computation in the source
("the computation of the folded Coxeter diagram is immediate", Lemmas 3.9, 3.10). -/

theorem pairing_isometry_left (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    {x : L.obj.obj.carrier} (hx : g.1 x = x) (y : L.obj.obj.carrier) :
    L.obj.obj.pairing x (g.1 y) = L.obj.obj.pairing x y := by
  have h := g.property x (g.1 y)
  rw [hx, isometry_apply_apply g hg y] at h
  exact h.symm

theorem pairing_isometry_right (g : OrthogonalGroup L.obj)
    {y : L.obj.obj.carrier} (hy : g.1 y = y) (x : L.obj.obj.carrier) :
    L.obj.obj.pairing (g.1 x) y = L.obj.obj.pairing x y := by
  have h := g.property x y
  rw [hy] at h
  exact h

/-- AEGS Lemma 3.4's identity `α_I² = 2 α² + 2 α · I α`, in the non-fixed case. -/
theorem pairing_folded_self_of_not_fixed (g : OrthogonalGroup L.obj)
    {x : L.obj.obj.carrier} (hx : g.1 x ≠ x) :
    L.obj.obj.pairing (foldedVector g x) (foldedVector g x) =
      2 * L.obj.obj.pairing x x + 2 * L.obj.obj.pairing x (g.1 x) := by
  rw [foldedVector_of_not_fixed g hx]
  have hsymm : L.obj.obj.pairing (g.1 x) x = L.obj.obj.pairing x (g.1 x) :=
    L.obj.property.2 _ _
  rw [BilinModuleCat.pairing_add_left, BilinModuleCat.pairing_add_right,
    BilinModuleCat.pairing_add_right, hsymm, g.property x x]
  ring

theorem pairing_folded_self_of_fixed (g : OrthogonalGroup L.obj)
    {x : L.obj.obj.carrier} (hx : g.1 x = x) :
    L.obj.obj.pairing (foldedVector g x) (foldedVector g x) = L.obj.obj.pairing x x := by
  rw [foldedVector_of_fixed g hx]

theorem pairing_folded_folded_of_not_fixed (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    {x : L.obj.obj.carrier} (hx : g.1 x ≠ x) {y : L.obj.obj.carrier} (hy : g.1 y ≠ y) :
    L.obj.obj.pairing (foldedVector g x) (foldedVector g y) =
      2 * L.obj.obj.pairing x y + 2 * L.obj.obj.pairing x (g.1 y) := by
  have hxy : L.obj.obj.pairing (g.1 x) y = L.obj.obj.pairing x (g.1 y) := by
    have h := g.property (g.1 x) y
    rw [isometry_apply_apply g hg] at h
    exact h.symm
  have hss : L.obj.obj.pairing (g.1 x) (g.1 y) = L.obj.obj.pairing x y := g.property x y
  rw [foldedVector_of_not_fixed g hx, foldedVector_of_not_fixed g hy,
    BilinModuleCat.pairing_add_left, BilinModuleCat.pairing_add_right,
    BilinModuleCat.pairing_add_right, hxy, hss]
  ring

theorem pairing_fixed_folded_of_fixed (g : OrthogonalGroup L.obj)
    {x : L.obj.obj.carrier} (_hx : x ∈ involutionFixedSubmodule g) {y : L.obj.obj.carrier}
    (hy : g.1 y = y) :
    L.obj.obj.pairing x (foldedVector g y) = L.obj.obj.pairing x y := by
  rw [foldedVector_of_fixed g hy]

theorem pairing_fixed_folded_of_not_fixed (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    {x : L.obj.obj.carrier} (hx : x ∈ involutionFixedSubmodule g) {y : L.obj.obj.carrier}
    (hy : g.1 y ≠ y) :
    L.obj.obj.pairing x (foldedVector g y) = 2 * L.obj.obj.pairing x y := by
  rw [mem_involutionFixedSubmodule_iff] at hx
  rw [foldedVector_of_not_fixed g hy, BilinModuleCat.pairing_add_right,
    pairing_isometry_left g hg hx y]
  ring

/-! ## The invariant part of the real form -/

/-- The invariant part of the real form, as the image of the invariant sublattice. -/
noncomputable def realFormFixedImage (g : OrthogonalGroup L.obj) :
    Set (realForm L).obj.carrier :=
  Set.range fun v : involutionFixedSubmodule g => toRealForm L (v : L.obj.obj.carrier)

theorem mem_realFormFixedImage_iff (g : OrthogonalGroup L.obj)
    {z : (realForm L).obj.carrier} :
    z ∈ realFormFixedImage g ↔ ∃ v : involutionFixedSubmodule g,
      toRealForm L (v : L.obj.obj.carrier) = z :=
  Iff.rfl

/-- The pairing of an invariant vector with the fold is the pairing with the root: this is the
step "the intersection of the positive cone with `α^⊥` is the same as with `α_J^⊥`" of AEGS
Lemma 3.8, in the fixed case. -/
theorem realForm_pairing_folded_of_fixed (g : OrthogonalGroup L.obj)
    (v : involutionFixedSubmodule g) {y : L.obj.obj.carrier} (hy : g.1 y = y) :
    (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier))
        (toRealForm L (foldedVector g y))
      = (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier)) (toRealForm L y) := by
  rw [foldedVector_of_fixed g hy]

/-- The same in the non-fixed case: the fold pairs by twice the root, which is why the *mirror*
and the two sides of the mirror are unchanged by folding and the edge weights of the folded
diagram are the normalized squares of `foldedVector`. -/
theorem realForm_pairing_folded_of_not_fixed (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (v : involutionFixedSubmodule g) {y : L.obj.obj.carrier} (hy : g.1 y ≠ y) :
    (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier))
        (toRealForm L (foldedVector g y))
      = 2 * (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier)) (toRealForm L y) := by
  rw [foldedVector_of_not_fixed g hy, toRealForm_add, BilinModuleCat.pairing_add_right,
    realFormPairing_toRealForm, realFormPairing_toRealForm]
  rw [show (L.obj.obj.pairing (v : L.obj.obj.carrier) (g.1 y) : ℝ)
      = (L.obj.obj.pairing (v : L.obj.obj.carrier) y : ℝ) from by
    rw [pairing_isometry_left g hg ((mem_involutionFixedSubmodule_iff g).mp v.2) y]]
  ring

/-- **The folded mirror is the mirror**: an invariant vector pairs to zero with `α^I` exactly when
it pairs to zero with `α`. -/
theorem realForm_pairing_folded_eq_zero_iff (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (v : involutionFixedSubmodule g) (y : L.obj.obj.carrier) :
    (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier))
        (toRealForm L (foldedVector g y)) = 0 ↔
      (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier)) (toRealForm L y) = 0 := by
  by_cases hy : g.1 y = y
  · rw [realForm_pairing_folded_of_fixed g v hy]
  · rw [realForm_pairing_folded_of_not_fixed g hg v hy, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h (by norm_num)
      · exact h
    · exact Or.inr

theorem realForm_pairing_folded_nonneg_iff (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (v : involutionFixedSubmodule g) (y : L.obj.obj.carrier) :
    0 ≤ (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier))
        (toRealForm L (foldedVector g y)) ↔
      0 ≤ (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier)) (toRealForm L y) := by
  by_cases hy : g.1 y = y
  · rw [realForm_pairing_folded_of_fixed g v hy]
  · rw [realForm_pairing_folded_of_not_fixed g hg v hy]
    constructor <;> intro h <;> linarith

theorem realForm_pairing_folded_pos_iff (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (v : involutionFixedSubmodule g) (y : L.obj.obj.carrier) :
    0 < (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier))
        (toRealForm L (foldedVector g y)) ↔
      0 < (realForm L).obj.pairing (toRealForm L (v : L.obj.obj.carrier)) (toRealForm L y) := by
  by_cases hy : g.1 y = y
  · rw [realForm_pairing_folded_of_fixed g v hy]
  · rw [realForm_pairing_folded_of_not_fixed g hg v hy]
    constructor <;> intro h <;> linarith

/-! ## The folded root set and its diagram -/

/-- The folded root family (AEGS Definition 3.7): the folded vectors of a root family. -/
noncomputable def foldedRootFamily (g : OrthogonalGroup L.obj) {ι : Type*}
    (r : ι → L.obj.obj.carrier) : ι → L.obj.obj.carrier :=
  fun i => foldedVector g (r i)

/-- The folded root set: the image of a root set under folding. -/
noncomputable def foldedRootSet (g : OrthogonalGroup L.obj) (R : Set L.obj.obj.carrier) :
    Set L.obj.obj.carrier :=
  foldedVector g '' R

theorem foldedRootSet_range (g : OrthogonalGroup L.obj) {ι : Type*}
    (r : ι → L.obj.obj.carrier) :
    foldedRootSet g (Set.range r) = Set.range (foldedRootFamily g r) := by
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨r i, ⟨i, rfl⟩, rfl⟩

/-- **The folded Coxeter diagram** (AEGS Definition 3.7): the Coxeter diagram of the folded
vectors that are again of negative square, with the normalized pairing-square edge weights. -/
noncomputable def foldedCoxeterDiagram (g : OrthogonalGroup L.obj) {ι : Type*}
    (r : ι → L.obj.obj.carrier)
    (hr : ∀ i, L.obj.obj.pairing (foldedRootFamily g r i) (foldedRootFamily g r i) < 0) :
    CoxeterDiagram ι :=
  coxeterDiagramOfRoots L (foldedRootFamily g r) hr

theorem foldedCoxeterDiagram_edges (g : OrthogonalGroup L.obj) {ι : Type*}
    (r : ι → L.obj.obj.carrier)
    (hr : ∀ i, L.obj.obj.pairing (foldedRootFamily g r i) (foldedRootFamily g r i) < 0)
    (i j : ι) :
    (foldedCoxeterDiagram g r hr).edges i j = coxeterDiagramOfRootsEdges L
      (foldedRootFamily g r) i j :=
  rfl

/-! ## The folding theorem for chamber cones (AEGS Lemma 3.8) -/

/-- **The folded roots cut out the trace of the chamber cone**: inside the invariant part of the
real form, the cone of the folded root set is the trace of the cone of the root set. This is the
step "the intersection of the positive cone `C(T_En)` with `α^⊥` is the same as with `α_J^⊥`" of
AEGS Lemma 3.8, with no hypothesis beyond the involution and the isometry property. -/
theorem mem_weylChamberCone_folded_iff (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (t : (realForm L).obj.carrier) (v : involutionFixedSubmodule g)
    (R : Set L.obj.obj.carrier) :
    toRealForm L (v : L.obj.obj.carrier) ∈ weylChamberCone L t (foldedRootSet g R) ↔
      toRealForm L (v : L.obj.obj.carrier) ∈ weylChamberCone L t R := by
  rw [mem_weylChamberCone_iff, mem_weylChamberCone_iff]
  constructor
  · rintro ⟨hu, hc⟩
    exact ⟨hu, fun r hr => (realForm_pairing_folded_nonneg_iff g hg v r).mp (hc _ ⟨r, hr, rfl⟩)⟩
  · rintro ⟨hu, hc⟩
    refine ⟨hu, fun s hs => ?_⟩
    obtain ⟨r, hr, rfl⟩ := hs
    exact (realForm_pairing_folded_nonneg_iff g hg v r).mpr (hc r hr)

/-- The same for the interior cone. -/
theorem mem_rootInteriorCone_folded_iff (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (t : (realForm L).obj.carrier) (v : involutionFixedSubmodule g)
    (R : Set L.obj.obj.carrier) :
    toRealForm L (v : L.obj.obj.carrier) ∈ rootInteriorCone L t (foldedRootSet g R) ↔
      toRealForm L (v : L.obj.obj.carrier) ∈ rootInteriorCone L t R := by
  rw [mem_rootInteriorCone_iff, mem_rootInteriorCone_iff]
  constructor
  · rintro ⟨hu, hc⟩
    exact ⟨hu, fun r hr => (realForm_pairing_folded_pos_iff g hg v r).mp (hc _ ⟨r, hr, rfl⟩)⟩
  · rintro ⟨hu, hc⟩
    refine ⟨hu, fun s hs => ?_⟩
    obtain ⟨r, hr, rfl⟩ := hs
    exact (realForm_pairing_folded_pos_iff g hg v r).mpr (hc r hr)

/-- **The folding theorem** (AEGS Lemma 3.8): let `R` be a wall set of a chamber of `W(M)`
(`IsChamberWithWalls`, `#23`) and `σ` an involution of `M`. Then, inside the invariant part of the
real form, the folded roots cut out exactly the chamber of any point of the interior cone of `R`:
the folded set is the wall set of that chamber of the invariant sublattice. -/
theorem chamberOf_folded_trace (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    (t : (realForm L).obj.carrier) (hpos : (integralSignature L).1 = 1)
    (ht : 0 < realFormQuadratic L t) (hR : IsChamberWithWalls L t R)
    {v : L.obj.obj.carrier} (hv : toRealForm L v ∈ rootInteriorCone L t R) :
    chamberOf L t (toRealForm L v) ∩ realFormFixedImage g =
      rootInteriorCone L t (foldedRootSet g R) ∩ realFormFixedImage g := by
  rw [IsChamberWithWalls.chamberOf_eq L t hpos ht hR hv]
  ext w
  constructor
  · rintro ⟨hw, u, hu⟩
    rw [← hu] at hw ⊢
    exact ⟨(mem_rootInteriorCone_folded_iff g hg t u R).mpr hw, u, rfl⟩
  · rintro ⟨hw, u, hu⟩
    rw [← hu] at hw ⊢
    exact ⟨(mem_rootInteriorCone_folded_iff g hg t u R).mp hw, u, rfl⟩

end LeanCategories.Lattices.Valued
