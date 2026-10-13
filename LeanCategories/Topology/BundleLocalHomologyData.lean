/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Homology with coefficients in a bundle of abelian groups

Definition-level realization of Hatcher FC07-C03-U152.

Hatcher defines C_n(X;E) from finite sums n_i sigma_i, where sigma_i is a
singular simplex and n_i is a lift of sigma_i to a bundle E -> X of abelian
groups. Lifts of a fixed simplex add pointwise in the fiber groups. The
boundary is the alternating sum of the restrictions of each lift to the
faces. H_n(X;E) is the resulting homology.

Sweep III records exactly this presentation without proving that pointwise
sums of lifts are continuous, that the alternating boundary squares to zero,
or that the cycles/mod-boundaries relation is an equivalence relation. The
groups of lifts, the boundary maps, and the homology quotient are selected
from source-exact predicates; the missing properties remain Sweep-IV results.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open CategoryTheory
open scoped BigOperators

universe u

/-- Hatcher's prerequisite bundle-of-abelian-groups data, expressed with
Mathlib's native local trivializations. -/
structure AbelianGroupBundleData
    (E X : Type u) [TopologicalSpace E] [TopologicalSpace X] where
  G : Type u
  [modelTopology : TopologicalSpace G]
  [modelAddCommGroup : AddCommGroup G]
  [modelDiscreteTopology : DiscreteTopology G]
  p : C(E, X)
  fiberAddCommGroup : ∀ x : X, AddCommGroup {e : E // p e = x}
  trivialization : ∀ x : X, Bundle.Trivialization G p
  mem_baseSet : ∀ x : X, x ∈ (trivialization x).baseSet

attribute [instance] AbelianGroupBundleData.modelTopology
  AbelianGroupBundleData.modelAddCommGroup
  AbelianGroupBundleData.modelDiscreteTopology

/-- Exact source predicate saying the chosen local trivializations are group
isomorphisms on fibers. The covering condition is recorded explicitly as
Hatcher's immediate consequence. -/
def IsAbelianGroupBundleData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) : Prop :=
  IsCoveringMap D.p ∧
    (∀ (x : X) (a b : {e : E // D.p e = x}),
      letI := D.fiberAddCommGroup x
      ((D.trivialization x) (((a + b : {e : E // D.p e = x}) : E))).2 =
        ((D.trivialization x) (a : E)).2 +
          ((D.trivialization x) (b : E)).2) ∧
    (∀ (x : X),
      letI := D.fiberAddCommGroup x
      ((D.trivialization x) (((0 : {e : E // D.p e = x}) : E))).2 = 0)

/-- The singular simplicial set used for the local-coefficient construction. -/
abbrev localCoefficientSSet
    (X : Type u) [TopologicalSpace X] : SSet.{u} :=
  TopCat.toSSet.obj (TopCat.of X)

/-- A lift of a singular simplex to the total group bundle. -/
structure LocalCoefficientLiftData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) {n : ℕ}
    (σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n))) where
  simplex : (localCoefficientSSet E).obj
    (Opposite.op (SimplexCategory.mk n))
  isLift :
    (TopCat.toSSet.map (TopCat.ofHom D.p)).app
      (Opposite.op (SimplexCategory.mk n)) simplex = σ

/-- Coordinate of a lifted simplex in the model group, using the source's
group-preserving local trivialization at the corresponding base point. -/
def localCoefficientLiftCoordinateData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) {n : ℕ}
    {σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n))}
    (l : LocalCoefficientLiftData D σ)
    (t : stdSimplex ℝ (Fin (n + 1))) : D.G :=
  let σc := TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk n)) σ
  let lc := TopCat.toSSetObjEquiv (TopCat.of E)
    (Opposite.op (SimplexCategory.mk n)) l.simplex
  ((D.trivialization (σc t)) (lc t)).2

/-- A lift is the zero lift when all its fiber coordinates are zero. -/
def IsZeroLocalCoefficientLiftData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) {n : ℕ}
    {σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n))}
    (l : LocalCoefficientLiftData D σ) : Prop :=
  ∀ t, localCoefficientLiftCoordinateData D l t = 0

/-- Pointwise sum relation for three lifts of the same base simplex. -/
def IsSumLocalCoefficientLiftData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) {n : ℕ}
    {σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n))}
    (a b c : LocalCoefficientLiftData D σ) : Prop :=
  ∀ t,
    localCoefficientLiftCoordinateData D c t =
      localCoefficientLiftCoordinateData D a t +
        localCoefficientLiftCoordinateData D b t

/-- Candidate abelian group of lifts of a fixed simplex. -/
structure LocalCoefficientLiftGroupCandidateData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) {n : ℕ}
    (σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n))) where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  classOf : LocalCoefficientLiftData D σ → carrier

attribute [instance] LocalCoefficientLiftGroupCandidateData.instAddCommGroup

/-- Exact specification of the pointwise abelian group of lifts. -/
def IsLocalCoefficientLiftGroupData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) {n : ℕ}
    (σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (P : LocalCoefficientLiftGroupCandidateData D σ) : Prop :=
  Function.Bijective P.classOf ∧
    (∀ l, P.classOf l = 0 ↔ IsZeroLocalCoefficientLiftData D l) ∧
    ∀ a b c,
      P.classOf c = P.classOf a + P.classOf b ↔
        IsSumLocalCoefficientLiftData D a b c

/-- Source-faithful lift-group presentation data for one singular simplex. -/
abbrev LocalCoefficientLiftGroupPresentationData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X)
    {n : ℕ}
    (σ : (localCoefficientSSet X).obj (Opposite.op (SimplexCategory.mk n))) :=
  {P : LocalCoefficientLiftGroupCandidateData D σ //
    IsLocalCoefficientLiftGroupData D σ P}

/-- A certified lift-group presentation for every singular simplex. -/
structure LocalCoefficientLiftGroupSystemData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (_hD : IsAbelianGroupBundleData D) where
  group : ∀ {n : ℕ}
    (σ : (localCoefficientSSet X).obj (Opposite.op (SimplexCategory.mk n))),
    LocalCoefficientLiftGroupPresentationData D σ

/-- The coefficient group of lifts of a fixed simplex. -/
abbrev LocalCoefficientLiftGroupData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    {n : ℕ}
    (σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n))) : Type u :=
  (L.group σ).1.carrier

/-- Hatcher's local-coefficient chain group C_n(X;E): the direct sum, over
base singular simplices, of their groups of lifts. -/
abbrev LocalCoefficientChainData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (n : ℕ) :=
  DirectSum
    ((localCoefficientSSet X).obj (Opposite.op (SimplexCategory.mk n)))
    (fun σ => LocalCoefficientLiftGroupData D hD L σ)

/-- Type of a candidate boundary C_{n+1}(X;E) -> C_n(X;E). -/
abbrev LocalCoefficientBoundaryHomData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (n : ℕ) :=
  LocalCoefficientChainData D hD L (n + 1) →+
    LocalCoefficientChainData D hD L n

/-- Exact alternating-face specification of Hatcher's local-coefficient
boundary. Face lifts are existentially specified rather than constructed,
so no lifting/naturality theorem enters Sweep III. -/
def IsLocalCoefficientBoundaryData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (n : ℕ) (d : LocalCoefficientBoundaryHomData D hD L n) : Prop :=
  letI : DecidableEq ((localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))) := Classical.decEq _
  letI : DecidableEq ((localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n))) := Classical.decEq _
  ∀ (σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk (n + 1))))
    (l : LocalCoefficientLiftData D σ),
    ∃ faces : ∀ i : Fin (n + 2),
        LocalCoefficientLiftData D ((localCoefficientSSet X).δ i σ),
      (∀ i, (faces i).simplex = (localCoefficientSSet E).δ i l.simplex) ∧
        d (DirectSum.of
          (fun τ => LocalCoefficientLiftGroupData D hD L τ) σ
          ((L.group σ).1.classOf l)) =
        ∑ i : Fin (n + 2),
          (-1 : ℤ) ^ i.val •
            DirectSum.of
              (fun τ => LocalCoefficientLiftGroupData D hD L τ)
              ((localCoefficientSSet X).δ i σ)
              ((L.group ((localCoefficientSSet X).δ i σ)).1.classOf (faces i))

/-- Source-faithful degree-`n+1 → n` boundary data. -/
abbrev LocalCoefficientBoundaryData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (n : ℕ) :=
  {d : LocalCoefficientBoundaryHomData D hD L n //
    IsLocalCoefficientBoundaryData D hD L n d}

/-- A certified boundary in every degree. Square-zero remains result content. -/
abbrev LocalCoefficientBoundarySystemData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD) :=
  ∀ n : ℕ, LocalCoefficientBoundaryData D hD L n

/-- Cycle predicate in degree n, with every degree-zero chain a cycle. -/
def IsLocalCoefficientCycleData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (B : LocalCoefficientBoundarySystemData D hD L)
    (n : ℕ) (x : LocalCoefficientChainData D hD L n) : Prop :=
  match n with
  | 0 => True
  | m + 1 => (B m).1 x = 0

/-- A local-coefficient cycle, without installing a subgroup structure. -/
structure LocalCoefficientCycleData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (B : LocalCoefficientBoundarySystemData D hD L)
    (n : ℕ) where
  chain : LocalCoefficientChainData D hD L n
  isCycle : IsLocalCoefficientCycleData D hD L B n chain

/-- Candidate quotient carrier for H_n(X;E). -/
structure LocalCoefficientHomologyCandidateData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (B : LocalCoefficientBoundarySystemData D hD L)
    (n : ℕ) where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  classOf : LocalCoefficientCycleData D hD L B n → carrier

attribute [instance] LocalCoefficientHomologyCandidateData.instAddCommGroup

/-- Exact cycles-mod-boundaries quotient specification for H_n(X;E).

The predicate states the quotient relation and the induced additive structure;
it does not prove that boundaries are cycles or that the relation is an
equivalence relation. -/
def IsLocalCoefficientHomologyData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (B : LocalCoefficientBoundarySystemData D hD L)
    (n : ℕ) (H : LocalCoefficientHomologyCandidateData D hD L B n) : Prop :=
  Function.Surjective H.classOf ∧
    (∀ x y,
      H.classOf x = H.classOf y ↔
        ∃ z : LocalCoefficientChainData D hD L (n + 1),
          x.chain - y.chain = (B n).1 z) ∧
    (∃ z : LocalCoefficientCycleData D hD L B n,
      z.chain = 0 ∧ H.classOf z = 0) ∧
    ∀ x y : LocalCoefficientCycleData D hD L B n,
      ∃ z : LocalCoefficientCycleData D hD L B n,
        z.chain = x.chain + y.chain ∧
          H.classOf z = H.classOf x + H.classOf y

/-- Source-faithful Hatcher homology quotient presentation data. -/
abbrev LocalCoefficientHomologyData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (B : LocalCoefficientBoundarySystemData D hD L)
    (n : ℕ) :=
  {H : LocalCoefficientHomologyCandidateData D hD L B n //
    IsLocalCoefficientHomologyData D hD L B n H}

/-- Source-facing carrier of homology with coefficients in the bundle E. -/
abbrev LocalCoefficientHomologyGroupData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    {L : LocalCoefficientLiftGroupSystemData D hD}
    {B : LocalCoefficientBoundarySystemData D hD L}
    {n : ℕ} (H : LocalCoefficientHomologyData D hD L B n) : Type u :=
  H.1.carrier

end LeanCategories.Topology
