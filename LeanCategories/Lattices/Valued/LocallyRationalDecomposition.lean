/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.RationalPolyhedralCone
public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.LocallyFinite
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Locally rational decompositions of the rational closure of a cone

Definitions 4.1 and 4.2 of E. Looijenga, *Compactifications defined by arrangements II:
locally symmetric varieties of type IV*, arXiv math/0201218v2 (2002), pp. 16-19, and the
support spaces of his Lemma-Definition 4.5, p. 19, over a finite-dimensional `ℚ`-vector
space `L`, on the rational cones of #37 (`RationalPolyhedralCone.lean`).

The carrier is the real form `L(ℝ) = L ⊗_ℚ ℝ`. It is carried as `ℝ ⊗[ℚ] L`, canonically
the same tensor product, because that is the order in which the scalar action of `ℝ` is
available: Mathlib's `TensorProduct.leftHasSMul` acts on the left factor, so `ℝ ⊗[ℚ] L` is
an `ℝ`-vector space with no extra structure.

## What is stated

* Definition 4.1 (p. 16): rational cones, and rational cone systems.
* Definition 4.2 (p. 17): the rational closure `C₊ = conv(L(ℚ) ∩ closure C)`, locally
  rational cones, locally rational decompositions, and the facial decomposition `Σ(bb)`.
* Lemma-Definition 4.5 (p. 19): the forms nonnegative on `τ` and zero on `σ`, and their
  common zero set, together with the two inclusions `span σ ≤ L_σ ≤ span τ` that pin the
  support space between the span of `σ` and the span of the cone above it.

## What is not in this file

* Example 4.3 (pp. 17-18): the quadratic cone, the arithmetic group `Γ` acting on the
  locally rational decompositions, and the theorem that a `Γ`-finite set of `ℚ`-hyperplanes
  meeting `C` gives the locally rational decomposition `Σ(H)`. The rationality of the cells
  of such an arrangement is Minkowski-Weyl over `ℚ` for cones cut out by finitely many
  rational inequalities; the repository has Minkowski-Weyl over `ℚ` in
  `ForMathlib/PointedConeMinkowskiWeyl.lean`, but not the transport of a cone so presented
  through the realification `ℝ ⊗[ℚ] L` that this file's carrier uses.
* The independence of `L_σ` from `τ` (Lemma-Definition 4.5, p. 19): the space is defined
  here as the intersection over the members above `σ`, and its value is proved when `σ`
  itself meets `C`, where it is `span σ` (`sigmaSupportSpace_eq_span_of_meets`). The
  source's proof for the remaining cones runs through the projection `π_I` on
  `I^⊥/I` for an isotropic line `I`.
* The local finiteness of the facial decomposition's traces
  (`facialDecomposition_isLocallyRational`): it is the hypothesis `HasLocallyFiniteTraces`
  there. In the Lorentzian case it holds because a convex cone in the null cone of a form of
  signature `(1, n)` lies in a totally isotropic subspace, so a rational cone meets at most
  one isotropic ray.

## LC-09 search record (2026-11-15)

Formalization-corpus queries, with the hits that decided the shape of the file.
`content:PointedCone convexHull rational`: no file. `content:locally finite hyperplane
arrangement`: TauCeti `Analysis/Convex/SimplicialComplex/Arrangement.lean` and
`Analysis/Convex/Polyhedron/SignCell/{Basic,Interior,Rational}.lean` (the sign-cell machine
of an affine arrangement, adapted there from Mei `Geometry/Convex/Polyhedron/SignCell.lean`,
commit `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, Apache 2.0). `content:SignCell`: TauCeti
`Polyhedron/SignCell/Basic.lean` — `signCell`, `weakSignCell`, `weakSignCellCone`,
`closure_signCell`, `realizedSignCellClosures` and the finiteness and extreme-subset lemmas
for a finite index set: the reference implementation of the cell construction of the
arrangement section below. `content:sign cell hyperplane`: LeanPool
`NandakumarRamanaRao/NRR/PowerDiagram/CellOverlap.lean`, unrelated (power diagrams).
`content:rational closure cone` and `content:IsFaceOf`: TauCeti
`Geometry/Toric/Algebraic/Cone/{Inf,Slice}.lean` (rational cones and faces, already ported
in `RationalPolyhedralCone.lean`). `content:semifan`,
`content:toroidal compactification cone` and `content:Fan support rational polyhedral`: no
file — Looijenga's semifans (his Definition 6.1, the next unit) are not formalized anywhere
in the corpus. `content:Lorentz cone` and `content:Baily-Borel`: no relevant hit (one
quantum-logical-framework `lakefile.lean`, one unrelated Shimura-curve file).

The cell construction below is written out here rather than ported, and the port of
TauCeti's three `SignCell` files is owed: with `weakSignCellCone` and
`realizedSignCellClosures` in the tree, the arrangement section becomes glue, and the
finiteness of the realized cells for a finite family comes for free there.

## References

* E. Looijenga, *Compactifications defined by arrangements II: locally symmetric varieties
  of type IV*, arXiv math/0201218v2 (2002), §4.
-/

@[expose] public section

open PointedCone

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ## The real form `L(ℝ) = L ⊗_ℚ ℝ` -/

/-- The real form of a `ℚ`-vector space: `L(ℝ) = L ⊗_ℚ ℝ`, carried as `ℝ ⊗[ℚ] L`. -/
abbrev realified (V : Type u) [AddCommGroup V] [Module ℚ V] : Type u := ℝ ⊗[ℚ] V

/-- The canonical topology of the real form: Mathlib's module topology. -/
noncomputable instance realifiedTopology : TopologicalSpace (realified V) :=
  moduleTopology ℝ _

instance realifiedIsModuleTopology : IsModuleTopology ℝ (realified V) := ⟨rfl⟩

instance realifiedContinuousAdd : ContinuousAdd (realified V) :=
  IsModuleTopology.toContinuousAdd ℝ (realified V)

instance realifiedContinuousSMul : ContinuousSMul ℝ (realified V) :=
  IsModuleTopology.toContinuousSMul ℝ (realified V)

/-- `L(ℚ) ⊂ L(ℝ)`: the rational points of the real form. -/
noncomputable def rationalPoint : V →ₗ[ℚ] (realified V) :=
  (TensorProduct.mk ℚ ℝ V) 1

theorem rationalPoint_apply (v : V) : rationalPoint v = (1 : ℝ) ⊗ₜ[ℚ] v := rfl

/-! ## Definition 4.1: rational cones and rational cone systems -/

/-- Looijenga, Definition 4.1, p. 16: a cone in `L(ℝ)` is *rational* when it is the convex
cone spanned by a finite subset of `L(ℚ)`. -/
def IsRationalCone (σ : PointedCone ℝ (realified V)) : Prop :=
  ∃ s : Finset V, σ = PointedCone.hull ℝ (rationalPoint '' (s : Set V))

/-- The points of a finite generating set that lie on a cone `τ` generate the intersection of
the cone hull of the set with `τ`. -/
theorem image_inter_eq_image_of_mem {s : Finset V} {τ : PointedCone ℝ (realified V)} :
    rationalPoint '' (s : Set V) ∩ (τ : Set (realified V)) =
      rationalPoint '' {v : V | v ∈ s ∧ rationalPoint v ∈ τ} := by
  ext x
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hvτ⟩
    exact ⟨v, ⟨hv, hvτ⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hvτ⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, hvτ⟩

/-- A face of a rational cone is rational: it is spanned by those of its rational generators
that lie on it (Looijenga, Definition 4.1, p. 16; #37's `IsLatticeRational.of_isFaceOf`). -/
theorem IsRationalCone.of_isFaceOf {σ τ : PointedCone ℝ (realified V)}
    (hσ : IsRationalCone σ) (hτ : τ.IsFaceOf σ) : IsRationalCone τ := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  refine ⟨s.filter fun v => rationalPoint v ∈ τ, ?_⟩
  refine (hτ.eq_hull_inter_of_eq_hull rfl).trans ?_
  rw [image_inter_eq_image_of_mem]
  congr 1
  ext v
  simp

/-- A rational cone has finitely many faces: each is spanned by a subset of one finite
generating set. -/
theorem finite_faces_of_isRationalCone {σ : PointedCone ℝ (realified V)}
    (hσ : IsRationalCone σ) :
    {F : PointedCone ℝ (realified V) | F.IsFaceOf σ}.Finite := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  refine Set.Finite.subset (s.powerset.finite_toSet.image fun t : Finset V =>
    PointedCone.hull ℝ (rationalPoint '' (t : Set V))) ?_
  rintro F hF
  have hface : F.IsFaceOf (PointedCone.hull ℝ (rationalPoint '' (s : Set V))) := hF
  refine ⟨s.filter fun v => rationalPoint v ∈ F, Finset.mem_powerset.2 (Finset.filter_subset _ _),
    ?_⟩
  refine (?_ : PointedCone.hull ℝ (rationalPoint '' ((s.filter fun v => rationalPoint v ∈ F
      : Finset V) : Set V)) = PointedCone.hull ℝ (rationalPoint '' (s : Set V)
        ∩ (F : Set (realified V)))).trans (hface.eq_hull_inter_of_eq_hull rfl).symm
  rw [image_inter_eq_image_of_mem]
  congr 1
  ext v
  simp

/-- Looijenga, Definition 4.1, p. 16: a *rational cone system* in `L(ℝ)` is a finite
collection of nondegenerate rational convex cones such that a face of a member is a member,
and any two members meet along a common face. -/
structure IsRationalConeSystem (S : Set (PointedCone ℝ (realified V))) : Prop where
  /-- A rational cone system is finite. -/
  finite : S.Finite
  /-- Every member is nondegenerate: it contains no affine line. -/
  salient : ∀ σ ∈ S, (σ : ConvexCone ℝ (realified V)).Salient
  /-- Every member is a rational cone. -/
  isRational : ∀ σ ∈ S, IsRationalCone σ
  /-- A face of a member is a member. -/
  mem_of_isFaceOf : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S
  /-- Two members meet along a common face. -/
  inf_isFaceOf_left : ∀ ⦃σ τ⦄, σ ∈ S → τ ∈ S → (σ ⊓ τ).IsFaceOf σ

namespace IsRationalConeSystem

variable {S : Set (PointedCone ℝ (realified V))}

/-- The intersection of two members of a rational cone system is a member. -/
theorem inf_mem (hS : IsRationalConeSystem S) {σ τ : PointedCone ℝ (realified V)}
    (hσ : σ ∈ S) (hτ : τ ∈ S) : σ ⊓ τ ∈ S :=
  hS.mem_of_isFaceOf hσ (hS.inf_isFaceOf_left hσ hτ)

/-- The intersection of two members is a face of the second one. -/
theorem inf_isFaceOf_right (hS : IsRationalConeSystem S) {σ τ : PointedCone ℝ (realified V)}
    (hσ : σ ∈ S) (hτ : τ ∈ S) : (σ ⊓ τ).IsFaceOf τ :=
  inf_comm σ τ ▸ hS.inf_isFaceOf_left hτ hσ

end IsRationalConeSystem

/-- The faces of a nondegenerate rational cone form a rational cone system: the facial
system of Definition 4.1, p. 16. -/
theorem isRationalConeSystem_faces {σ : PointedCone ℝ (realified V)} (hσ : IsRationalCone σ)
    (hσ' : (σ : ConvexCone ℝ (realified V)).Salient) :
    IsRationalConeSystem {F : PointedCone ℝ (realified V) | F.IsFaceOf σ} where
  finite := finite_faces_of_isRationalCone hσ
  salient F hF := hσ'.anti fun x hx => hF.le hx
  isRational F hF := IsRationalCone.of_isFaceOf (σ := σ) (τ := F) hσ hF
  mem_of_isFaceOf := by
    intro _ _ G hG
    exact hG.trans G
  inf_isFaceOf_left := by
    intro A B hA hB
    exact (IsFaceOf.isFaceOf_iff_le (hA.inf_left hB) hA).2 inf_le_left

/-! ## Definition 4.2: the rational closure and locally rational decompositions -/

/-- Looijenga, Definition 4.2, p. 17: the *rational closure* `C₊` of a convex cone `C` is the
convex hull of `L(ℚ) ∩ closure C`. The convex hull of a set of rational points of a cone is
the cone it generates, which is how it is carried here. -/
noncomputable def rationalClosure (C : PointedCone ℝ (realified V)) :
    PointedCone ℝ (realified V) :=
  PointedCone.hull ℝ (rationalPoint '' (Set.univ : Set V) ∩ closure (C : Set (realified V)))

/-- Looijenga, Definition 4.2, p. 17: a cone is *locally rational* in `C₊` when its
intersection with every rational subcone of `C₊` is rational. -/
def IsLocallyRationalCone (Cplus σ : PointedCone ℝ (realified V)) : Prop :=
  ∀ P : PointedCone ℝ (realified V), IsRationalCone P → P ≤ Cplus → IsRationalCone (σ ⊓ P)

/-- A cone whose traces on every rational subcone of `C₊` are locally finite. -/
def HasLocallyFiniteTraces (Cplus : PointedCone ℝ (realified V))
    (S : Set (PointedCone ℝ (realified V))) : Prop :=
  ∀ P : PointedCone ℝ (realified V), IsRationalCone P → P ≤ Cplus →
    LocallyFinite fun σ : {σ // σ ∈ S} =>
      ((σ.1 : PointedCone ℝ (realified V)) : Set (realified V)) ∩ (P : Set (realified V))

/-- Looijenga, Definition 4.2, p. 17: a *locally rational decomposition* of `C₊` is a
collection of convex cones whose union is `C₊` and whose restriction to every rational
subcone of `C₊` is a rational cone system. The finiteness of a rational cone system
(Definition 4.1, p. 16) is read locally, as local finiteness on each rational subcone: that
is the reading under which the facial decomposition below is a locally rational
decomposition, and it is the property the later sections of the source use. -/
structure IsLocallyRationalDecomposition (Cplus : PointedCone ℝ (realified V))
    (S : Set (PointedCone ℝ (realified V))) : Prop where
  /-- The union of the members is `C₊`. -/
  union_eq : (⋃ σ ∈ S, (σ : Set (realified V))) = (Cplus : Set (realified V))
  /-- Every member is a locally rational cone in `C₊`. -/
  isLocallyRational : ∀ σ ∈ S, IsLocallyRationalCone Cplus σ
  /-- The traces on every rational subcone of `C₊` are locally finite. -/
  locallyFinite : HasLocallyFiniteTraces Cplus S

/-- The facial decomposition `Σ(bb)` of `C₊`: its faces, `C₊` itself included (Looijenga,
Definition 4.2, p. 17). -/
def facialDecomposition (Cplus : PointedCone ℝ (realified V)) :
    Set (PointedCone ℝ (realified V)) :=
  {σ | σ.IsFaceOf Cplus}

/-- A face of `C₊` intersected with a subcone `P ≤ C₊` is a face of `P`. -/
theorem isFaceOf_inf_of_le {σ P : PointedCone ℝ (realified V)} (hσ : σ.IsFaceOf P) :
    (σ ⊓ P).IsFaceOf P :=
  hσ.inf_left (PointedCone.IsFaceOf.refl P)

/-- A face of `C₊` has rational traces on a rational cone: its intersection with a rational
subcone `P ≤ C₊` is a face of `P`, and faces of rational cones are rational. -/
theorem isLocallyRationalCone_facialDecomposition (Cplus : PointedCone ℝ (realified V))
    {σ : PointedCone ℝ (realified V)} (hσ : σ ∈ facialDecomposition Cplus) :
    IsLocallyRationalCone Cplus σ := by
  intro P hP hPC
  have hface : (σ ⊓ P).IsFaceOf P := by
    refine ⟨inf_le_right, ?_⟩
    intro x y a hx hy ha hxy
    exact ⟨hσ.mem_of_smul_add_mem (hPC hx) (hPC hy) ha hxy.1, hx⟩
  exact hP.of_isFaceOf hface

/-- The facial decomposition covers `C₊`: `C₊` is a face of itself. -/
theorem union_facialDecomposition (Cplus : PointedCone ℝ (realified V)) :
    (⋃ σ ∈ facialDecomposition Cplus, (σ : Set (realified V))) = (Cplus : Set (realified V)) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · refine Set.iUnion_subset fun σ => Set.iUnion_subset fun hσ => ?_
    exact hσ.le
  · intro x hx
    exact Set.mem_iUnion.2 ⟨Cplus, Set.mem_iUnion.2 ⟨PointedCone.IsFaceOf.refl Cplus, hx⟩⟩

/-- **The facial decomposition `Σ(bb)` is a locally rational decomposition** (Looijenga,
Definition 4.2, p. 17), once its traces on rational subcones are locally finite. -/
theorem facialDecomposition_isLocallyRational (Cplus : PointedCone ℝ (realified V))
    (hfin : HasLocallyFiniteTraces Cplus (facialDecomposition Cplus)) :
    IsLocallyRationalDecomposition Cplus (facialDecomposition Cplus) where
  union_eq := union_facialDecomposition Cplus
  isLocallyRational := fun _ hσ => isLocallyRationalCone_facialDecomposition Cplus hσ
  locallyFinite := hfin

/-- `Σ(bb)` is the coarsest locally rational decomposition: every cone of any locally
rational decomposition of `C₊` lies in a member of `Σ(bb)` (Looijenga, Definition 4.2,
p. 17). -/
theorem facialDecomposition_coarsest (Cplus : PointedCone ℝ (realified V))
    {S : Set (PointedCone ℝ (realified V))} (hS : IsLocallyRationalDecomposition Cplus S) :
    ∀ σ ∈ S, ∃ F ∈ facialDecomposition Cplus, σ ≤ F := by
  intro σ hσ
  refine ⟨Cplus, PointedCone.IsFaceOf.refl Cplus, ?_⟩
  intro x hx
  have hunion : (⋃ σ ∈ S, (σ : Set (realified V))) = (Cplus : Set (realified V)) :=
    hS.union_eq
  have hx' : x ∈ (⋃ σ ∈ S, (σ : Set (realified V))) :=
    Set.mem_iUnion.2 ⟨σ, Set.mem_iUnion.2 ⟨hσ, hx⟩⟩
  rw [hunion] at hx'
  simpa using hx'

/-! ## Lemma-Definition 4.5: the support space of a cone of a decomposition -/

/-- Looijenga, Lemma-Definition 4.5, p. 19: the real linear forms that are nonnegative on
`τ` and zero on `σ`. -/
def supportForms (τ σ : PointedCone ℝ (realified V)) : Set ((realified V) →ₗ[ℝ] ℝ) :=
  {φ | (∀ x ∈ τ, 0 ≤ φ x) ∧ (∀ x ∈ σ, φ x = 0)}

theorem mem_supportForms {τ σ : PointedCone ℝ (realified V)} {φ : (realified V) →ₗ[ℝ] ℝ} :
    φ ∈ supportForms τ σ ↔ (∀ x ∈ τ, 0 ≤ φ x) ∧ (∀ x ∈ σ, φ x = 0) :=
  Iff.rfl

/-- Looijenga, Lemma-Definition 4.5, p. 19: the common zero set of the real linear forms on
`L(ℝ)` that are nonnegative on `τ` and zero on `σ`. -/
noncomputable def supportSpace (τ σ : PointedCone ℝ (realified V)) :
    Submodule ℝ (realified V) :=
  ⨅ (φ : supportForms τ σ), LinearMap.ker (φ : (realified V) →ₗ[ℝ] ℝ)

theorem mem_supportSpace {τ σ : PointedCone ℝ (realified V)} {x : realified V} :
    x ∈ supportSpace τ σ ↔ ∀ φ ∈ supportForms τ σ, φ x = 0 := by
  rw [supportSpace, Submodule.mem_iInf]
  exact ⟨fun h φ hφ => h ⟨φ, hφ⟩, fun h φ => h φ.1 φ.2⟩

/-- The support space contains the span of `σ`: every form of `supportForms τ σ` vanishes on
`σ` (Looijenga, Lemma-Definition 4.5, p. 19). -/
theorem span_le_supportSpace {σ τ : PointedCone ℝ (realified V)} (_hστ : σ ≤ τ) :
    Submodule.span ℝ (σ : Set (realified V)) ≤ supportSpace τ σ := by
  refine Submodule.span_le.2 fun x hx => ?_
  exact mem_supportSpace.2 fun φ hφ => (mem_supportForms.1 hφ).2 x hx

/-- The support space is contained in the span of `τ`: a point outside the span of `τ` is
separated from `τ` by a form vanishing on `τ`, which is a form of `supportForms τ σ`
(Looijenga, Lemma-Definition 4.5, p. 19). -/
theorem supportSpace_le_span {σ τ : PointedCone ℝ (realified V)} (hστ : σ ≤ τ) :
    supportSpace τ σ ≤ Submodule.span ℝ (τ : Set (realified V)) := by
  intro x hx
  by_contra hxτ
  obtain ⟨f, hf0, hfker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (p := Submodule.span ℝ (τ : Set (realified V)))
      hxτ (inferInstance : Module.Projective ℝ
        ((realified V) ⧸ Submodule.span ℝ (τ : Set (realified V))))
  have hfτ : ∀ y ∈ τ, f y = 0 := by
    intro y hy
    have hmem : f y ∈ (Submodule.span ℝ (τ : Set (realified V))).map f :=
      ⟨y, Submodule.subset_span hy, rfl⟩
    rw [hfker] at hmem
    simpa using hmem
  have hφ : f ∈ supportForms τ σ :=
    ⟨fun y hy => by rw [hfτ y hy], fun y hy => hfτ y (hστ hy)⟩
  exact hf0 (mem_supportSpace.1 hx f hφ)

/-- The support space of `σ` relative to `τ` is the span of `σ` when `τ = σ`. -/
theorem supportSpace_self (σ : PointedCone ℝ (realified V)) :
    supportSpace σ σ = Submodule.span ℝ (σ : Set (realified V)) :=
  le_antisymm (supportSpace_le_span le_rfl) (span_le_supportSpace le_rfl)

/-- The support space is monotone in `τ`: a form nonnegative on a larger cone is nonnegative
on a smaller one, so the common zero set grows with the cone. -/
theorem supportSpace_mono {σ τ τ' : PointedCone ℝ (realified V)} (hτ : τ ≤ τ') :
    supportSpace τ σ ≤ supportSpace τ' σ := by
  intro x hx
  refine mem_supportSpace.2 fun φ hφ => ?_
  exact mem_supportSpace.1 hx φ ⟨fun y hy => hφ.1 y (hτ hy), hφ.2⟩

/-- The members of a decomposition that contain `σ` and meet the open cone `C`:
the cones `τ` over which Looijenga, Lemma-Definition 4.5, p. 19, states the support space. -/
def supportIndex (C : PointedCone ℝ (realified V)) (S : Set (PointedCone ℝ (realified V)))
    (σ : PointedCone ℝ (realified V)) : Type u :=
  {τ : PointedCone ℝ (realified V) // τ ∈ S ∧ σ ≤ τ ∧
    ((τ : Set (realified V)) ∩ (C : Set (realified V))).Nonempty}

/-- The support space of `σ` in a decomposition. Looijenga's Lemma-Definition 4.5, p. 19,
gives `L_σ` as the common value of `supportSpace τ σ` over the members `τ ≥ σ` meeting `C`;
that common value is carried here as their intersection. -/
noncomputable def sigmaSupportSpace (C : PointedCone ℝ (realified V))
    (S : Set (PointedCone ℝ (realified V))) (σ : PointedCone ℝ (realified V)) :
    Submodule ℝ (realified V) :=
  ⨅ (τ : supportIndex C S σ), supportSpace τ.1 σ

/-- The support space of `σ` is contained in the space of every member above it. -/
theorem sigmaSupportSpace_le {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ τ : PointedCone ℝ (realified V)}
    (hτ : τ ∈ S) (hστ : σ ≤ τ)
    (hC : ((τ : Set (realified V)) ∩ (C : Set (realified V))).Nonempty) :
    sigmaSupportSpace C S σ ≤ supportSpace τ σ :=
  iInf_le (fun τ : supportIndex C S σ => supportSpace τ.1 σ) ⟨τ, hτ, hστ, hC⟩

/-- The support space of `σ` contains the span of `σ`. -/
theorem span_le_sigmaSupportSpace {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (_τ : supportIndex C S σ) :
    Submodule.span ℝ (σ : Set (realified V)) ≤ sigmaSupportSpace C S σ :=
  le_iInf fun τ' => span_le_supportSpace τ'.2.2.1

/-- **The support space of a cone that meets the open cone is the span of that cone**: the
member `σ` itself is one of the cones over which the intersection is taken, and its space is
`span σ` (Looijenga, Lemma-Definition 4.5, p. 19). -/
theorem sigmaSupportSpace_eq_span_of_meets {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (hσ : σ ∈ S) (hC : ((σ : Set (realified V)) ∩ (C : Set (realified V))).Nonempty) :
    sigmaSupportSpace C S σ = Submodule.span ℝ (σ : Set (realified V)) := by
  refine le_antisymm ?_ (span_le_sigmaSupportSpace ⟨σ, hσ, le_rfl, hC⟩)
  exact (sigmaSupportSpace_le (σ := σ) (τ := σ) hσ le_rfl hC).trans_eq (supportSpace_self σ)

/-! ## The decomposition attached to an arrangement of hyperplanes

Looijenga, Example 4.3 (b), pp. 17-18: a collection `H` of hyperplanes through the origin
that meet `C` cuts `C₊` into the closures of the components of `C₊` minus their union, the
decomposition `Σ(H)`. The cones are the weak sign cells of the family of linear forms
defining the hyperplanes; the construction is here, its local rationality and local
finiteness are not (see the module docstring). -/

section Arrangement

variable {ι : Type*} (φ : ι → (realified V) →ₗ[ℝ] ℝ)

/-- The closed cone of a sign pattern: the locus where each form is zero, nonpositive or
nonnegative according to the pattern. -/
noncomputable def arrangementCone (s : ι → SignType) : PointedCone ℝ (realified V) where
  carrier := {x | ∀ i, match s i with
    | .zero => φ i x = 0
    | .neg => φ i x ≤ 0
    | .pos => 0 ≤ φ i x}
  zero_mem' := by
    intro i
    cases h : s i <;> simp
  add_mem' := by
    intro x y hx hy i
    have hx' := hx i
    have hy' := hy i
    have hsum : φ i (x + y) = φ i x + φ i y := map_add _ _ _
    cases h : s i <;> simp only [h] at hx' hy' ⊢
    · rw [hsum, hx', hy', add_zero]
    · rw [hsum]; linarith
    · rw [hsum]; linarith
  smul_mem' := by
    intro a x hx i
    have hx' := hx i
    have ha : (0 : ℝ) ≤ (a : ℝ) := a.2
    have hsmul : φ i (a • x) = (a : ℝ) * φ i x := by
      change φ i ((a : ℝ) • x) = (a : ℝ) * φ i x
      rw [map_smul, smul_eq_mul]
    cases h : s i <;> simp only [h] at hx' ⊢
    · rw [hsmul, hx', mul_zero]
    · rw [hsmul]
      exact mul_nonpos_of_nonneg_of_nonpos ha hx'
    · rw [hsmul]
      exact mul_nonneg ha hx'

theorem mem_arrangementCone {s : ι → SignType} {x : realified V} :
    x ∈ arrangementCone φ s ↔ ∀ i, match s i with
      | .zero => φ i x = 0
      | .neg => φ i x ≤ 0
      | .pos => 0 ≤ φ i x :=
  Iff.rfl

/-- The sign pattern realized by a point. -/
noncomputable def signPattern (x : realified V) : ι → SignType :=
  fun i => SignType.sign (φ i x)

theorem mem_arrangementCone_signPattern (x : realified V) :
    x ∈ arrangementCone φ (signPattern φ x) := by
  intro i
  have hs : signPattern φ x i = SignType.sign (φ i x) := rfl
  rw [hs]
  cases h : SignType.sign (φ i x) with
  | zero => simpa using sign_eq_zero_iff.1 h
  | neg => simpa using le_of_lt (sign_eq_neg_one_iff.1 h)
  | pos => simpa using le_of_lt (sign_eq_one_iff.1 h)

/-- **The decomposition `Σ(H)` of `C₊` attached to a family of forms**: the closed sign cells
intersected with the rational closure (Looijenga, Example 4.3 (b), pp. 17-18). -/
noncomputable def arrangementDecomposition (Cplus : PointedCone ℝ (realified V)) :
    Set (PointedCone ℝ (realified V)) :=
  {σ | ∃ s : ι → SignType, σ = arrangementCone φ s ⊓ Cplus}

theorem union_arrangementDecomposition (Cplus : PointedCone ℝ (realified V)) :
    (⋃ σ ∈ arrangementDecomposition φ Cplus, (σ : Set (realified V)))
      = (Cplus : Set (realified V)) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · refine Set.iUnion_subset fun σ => Set.iUnion_subset fun hσ => ?_
    obtain ⟨s, rfl⟩ := hσ
    exact inf_le_right
  · intro x hx
    refine Set.mem_iUnion.2 ⟨arrangementCone φ (signPattern φ x) ⊓ Cplus,
      Set.mem_iUnion.2 ⟨⟨signPattern φ x, rfl⟩, ?_⟩⟩
    exact ⟨mem_arrangementCone_signPattern φ x, hx⟩

end Arrangement

end LeanCategories.Lattices.Valued
