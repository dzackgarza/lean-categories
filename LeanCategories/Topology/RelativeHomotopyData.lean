/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.HomotopyGroups

/-!
# Relative homotopy data

Definition-level realization of Hatcher FC07-C04-U007.

For a based pair `x₀ ∈ A ⊆ X` and `n > 0`, a relative `n`-cube sends the
whole boundary of `I^n` into `A` and sends `J^{n-1}` to `x₀`, where
`J^{n-1}` is the union of all faces except the distinguished last-coordinate
zero face. Relative homotopies preserve the same two conditions.

Sweep III records the relative maps, their homotopy-class quotient, the
source concatenation formula, and a candidate group constrained by that
formula for `n ≥ 2`. It does not prove that relative homotopy is an
equivalence relation, that concatenation descends through the quotient, the
group laws, or commutativity for `n ≥ 3`; those are result-layer obligations.
-/

@[expose] public noncomputable section

open scoped Topology Topology.Homotopy

namespace LeanCategories.Topology

universe u

/-- The distinguished last coordinate in Hatcher's positive-dimensional
relative cube. -/
def relativeHomotopyLastCoordinate (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

/-- Hatcher's `J^{n-1}`: every cubical face except the distinguished
last-coordinate zero face. -/
def relativeHomotopyJData (n : ℕ) (hn : 0 < n) :
    Set (Fin n → unitInterval) :=
  {y |
    y (relativeHomotopyLastCoordinate n hn) = 1 ∨
      ∃ i : Fin n,
        i ≠ relativeHomotopyLastCoordinate n hn ∧
          (y i = 0 ∨ y i = 1)}

/-- A relative `n`-cube for `(X,A,x₀)`: its boundary lies in `A`, and
all of `J^{n-1}` is sent to the basepoint. -/
structure RelativeGenLoopData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (n : ℕ) (hn : 0 < n) where
  toContinuousMap : C(Fin n → unitInterval, X)
  boundary_mem :
    ∀ y ∈ Cube.boundary (Fin n), toContinuousMap y ∈ A
  fixed_boundary :
    ∀ y ∈ relativeHomotopyJData n hn, toContinuousMap y = x0

/-- The constant relative cube at the distinguished point. -/
def relativeGenLoopConstData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) :
    RelativeGenLoopData X A x0 n hn where
  toContinuousMap := ContinuousMap.const _ x0
  boundary_mem := by
    intro _ _
    exact hx0
  fixed_boundary := by
    intro _ _
    rfl

namespace RelativeGenLoopData

/-- Homotopy of relative cubes: throughout the homotopy the cubical boundary
stays in `A` and `J^{n-1}` stays at `x₀`. -/
def Homotopic
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    {n : ℕ} {hn : 0 < n}
    (f g : RelativeGenLoopData X A x0 n hn) : Prop :=
  ∃ H : C(unitInterval × (Fin n → unitInterval), X),
    (∀ y, H (0, y) = f.toContinuousMap y) ∧
      (∀ y, H (1, y) = g.toContinuousMap y) ∧
        (∀ t y, y ∈ Cube.boundary (Fin n) → H (t, y) ∈ A) ∧
          ∀ t y, y ∈ relativeHomotopyJData n hn → H (t, y) = x0

end RelativeGenLoopData

/-- The raw homotopy-class carrier of relative `n`-cubes.

The later result that `RelativeGenLoopData.Homotopic` is an equivalence
relation identifies this quotient with the usual set of relative homotopy
classes. -/
abbrev RelativeHomotopyClassData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (n : ℕ) (hn : 0 < n) :=
  Quot (fun f g : RelativeGenLoopData X A x0 n hn =>
    RelativeGenLoopData.Homotopic f g)

/-- The relative homotopy class of a representative. -/
def relativeHomotopyClassMkData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    {n : ℕ} {hn : 0 < n}
    (f : RelativeGenLoopData X A x0 n hn) :
    RelativeHomotopyClassData X A x0 n hn :=
  Quot.mk _ f

/-- The distinguished class represented by the constant relative cube. -/
def relativeHomotopyBaseClassData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) :
    RelativeHomotopyClassData X A x0 n hn :=
  relativeHomotopyClassMkData
    (relativeGenLoopConstData X A x0 hx0 n hn)

/-- Exact pointwise graph of concatenation of two relative cubes in coordinate
`i`, using the same cubical subdivision as Mathlib's absolute
`GenLoop.transAt`. -/
def IsRelativeGenLoopConcatData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    {n : ℕ} {hn : 0 < n}
    (i : Fin n)
    (f g h : RelativeGenLoopData X A x0 n hn) : Prop :=
  ∀ t,
    h.toContinuousMap t =
      if (t i : ℝ) ≤ 1 / 2 then
        f.toContinuousMap
          (Function.update t i
            (Set.projIcc 0 1 zero_le_one (2 * t i)))
      else
        g.toContinuousMap
          (Function.update t i
            (Set.projIcc 0 1 zero_le_one (2 * t i - 1)))

/-- Source-faithful relative-cube concatenation data: a candidate relative
cube together with the exact pointwise concatenation graph. -/
abbrev RelativeGenLoopConcatData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    (hx0 : x0 ∈ A) {n : ℕ} {hn : 0 < n}
    (i : Fin n)
    (f g : RelativeGenLoopData X A x0 n hn) :=
  {h : RelativeGenLoopData X A x0 n hn //
    IsRelativeGenLoopConcatData i f g h}

/-- Hatcher's canonical concatenation coordinate for `n ≥ 2`: the first
coordinate, which is distinct from the distinguished last coordinate. -/
def relativeHomotopyConcatCoordinate (n : ℕ) (h2 : 2 ≤ n) : Fin n :=
  ⟨0, by omega⟩

/-- Certified concatenation data for every pair of relative representatives. -/
abbrev RelativeGenLoopConcatSystemData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) :=
  ∀ f g : RelativeGenLoopData X A x0 n hn,
    RelativeGenLoopConcatData hx0
      (relativeHomotopyConcatCoordinate n h2) f g

/-- A candidate realization of the relative homotopy group. The carrier is
equipped with group structure, while `classOf` records how the raw relative
homotopy quotient is to be identified with it. -/
structure RelativeHomotopyGroupCandidateData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (n : ℕ) (hn : 0 < n) where
  carrier : Type u
  [instGroup : Group carrier]
  classOf : RelativeHomotopyClassData X A x0 n hn → carrier

attribute [instance] RelativeHomotopyGroupCandidateData.instGroup

instance
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (n : ℕ) (hn : 0 < n) :
    Nonempty (RelativeHomotopyGroupCandidateData X A x0 n hn) :=
  ⟨⟨PUnit.{u + 1}, fun _ => 1⟩⟩

/-- Exact source specification for the group structure on relative homotopy
classes in degree `n ≥ 2`.

The specification asks for a bijective identification with the raw quotient,
takes the constant class to the identity, and identifies multiplication with
concatenation in the first non-distinguished coordinate. No existence,
well-definedness, or group-law proof is supplied here. -/
def IsRelativeHomotopyGroupData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    (C : RelativeGenLoopConcatSystemData X A x0 hx0 n hn h2)
    (P : RelativeHomotopyGroupCandidateData X A x0 n hn) : Prop :=
  Function.Bijective P.classOf ∧
    P.classOf (relativeHomotopyBaseClassData X A x0 hx0 n hn) = 1 ∧
      ∀ f g : RelativeGenLoopData X A x0 n hn,
        P.classOf
            (relativeHomotopyClassMkData
              (C f g).1) =
          P.classOf (relativeHomotopyClassMkData f) *
            P.classOf (relativeHomotopyClassMkData g)

/-- Source-faithful relative homotopy group presentation data in degree at
least two. -/
abbrev RelativeHomotopyGroupData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    (C : RelativeGenLoopConcatSystemData X A x0 hx0 n hn h2) :=
  {P : RelativeHomotopyGroupCandidateData X A x0 n hn //
    IsRelativeHomotopyGroupData X A x0 hx0 n hn h2 C P}

/-- Source-facing carrier of supplied valid relative homotopy group data. -/
abbrev RelativeHomotopyGroupCarrierData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    {C : RelativeGenLoopConcatSystemData X A x0 hx0 n hn h2}
    (P : RelativeHomotopyGroupData X A x0 hx0 n hn h2 C) : Type u :=
  P.1.carrier

/-- Hatcher's degree-one relative homotopy object, which is only a pointed
set. -/
abbrev RelativeHomotopyPointedSetData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X) :=
  RelativeHomotopyClassData X A x0 1 (Nat.zero_lt_succ 0)

/-- Basepoint of Hatcher's degree-one relative homotopy pointed set. -/
def relativeHomotopyPointedBaseData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) :
    RelativeHomotopyPointedSetData X A x0 :=
  relativeHomotopyBaseClassData X A x0 hx0 1 (Nat.zero_lt_succ 0)

/-- The coordinates of the distinguished zero face of a positive-dimensional
relative cube.  This is canonically an `(n - 1)`-element indexing type. -/
abbrev RelativeHomotopyBoundaryIndex (n : ℕ) (hn : 0 < n) :=
  {j : Fin n // j ≠ relativeHomotopyLastCoordinate n hn}

/-- Exact source graph for restricting a relative cube to its distinguished
zero face.  The target is an ordinary generalized loop in the subspace `A`;
the complement of the distinguished coordinate is the source's
`(n - 1)`-cube. -/
def IsRelativeHomotopyBoundaryRepresentativeData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    (hx0 : x0 ∈ A) {n : ℕ} {hn : 0 < n}
    (f : RelativeGenLoopData X A x0 n hn)
    (g : GenLoop (RelativeHomotopyBoundaryIndex n hn) A ⟨x0, hx0⟩) : Prop :=
  ∀ t,
    (g t : X) =
      f.toContinuousMap
        (Cube.insertAt (relativeHomotopyLastCoordinate n hn) (0, t))

/-- Source-faithful distinguished-face representative data. -/
abbrev RelativeHomotopyBoundaryRepresentativeData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    (hx0 : x0 ∈ A) {n : ℕ} {hn : 0 < n}
    (f : RelativeGenLoopData X A x0 n hn) :=
  {g : GenLoop (RelativeHomotopyBoundaryIndex n hn) A ⟨x0, hx0⟩ //
    IsRelativeHomotopyBoundaryRepresentativeData hx0 f g}

/-- Certified distinguished-face representatives for every relative cube. -/
abbrev RelativeHomotopyBoundaryRepresentativeSystemData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) :=
  ∀ f : RelativeGenLoopData X A x0 n hn,
    RelativeHomotopyBoundaryRepresentativeData hx0 f

/-- The ordinary homotopy class of the distinguished-face restriction of a
relative cube. -/
def relativeHomotopyBoundaryClassData
    {X : Type u} [TopologicalSpace X] {A : Set X} {x0 : X}
    (hx0 : x0 ∈ A) {n : ℕ} {hn : 0 < n}
    (R : RelativeHomotopyBoundaryRepresentativeSystemData hx0 n hn)
    (f : RelativeGenLoopData X A x0 n hn) :
    HomotopyGroup (RelativeHomotopyBoundaryIndex n hn) A ⟨x0, hx0⟩ :=
  Quotient.mk _ (R f).1

/-- Exact source specification for the boundary map on raw relative homotopy
classes: a class represented by `f` is sent to the class of the distinguished
face of `f`.  Well-definedness on representatives is a Sweep-IV result. -/
def IsRelativeHomotopyBoundaryClassData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n)
    (R : RelativeHomotopyBoundaryRepresentativeSystemData hx0 n hn)
    (δ : RelativeHomotopyClassData X A x0 n hn →
      HomotopyGroup (RelativeHomotopyBoundaryIndex n hn) A ⟨x0, hx0⟩) : Prop :=
  ∀ f : RelativeGenLoopData X A x0 n hn,
    δ (relativeHomotopyClassMkData f) =
      relativeHomotopyBoundaryClassData hx0 R f

/-- Source-faithful raw relative-boundary class-map data. -/
abbrev RelativeHomotopyBoundaryClassMapData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n)
    (R : RelativeHomotopyBoundaryRepresentativeSystemData hx0 n hn) :=
  {δ :
      RelativeHomotopyClassData X A x0 n hn →
        HomotopyGroup (RelativeHomotopyBoundaryIndex n hn) A ⟨x0, hx0⟩ //
    IsRelativeHomotopyBoundaryClassData X A x0 hx0 n hn R δ}

/-- Exact source specification for the boundary map on Hatcher's selected
group carrier in degree `n ≥ 2`.  It agrees with distinguished-face
restriction on every represented relative cube.  The assertion that this map
is a group homomorphism is result content and is deliberately absent. -/
def IsRelativeHomotopyBoundaryData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    (C : RelativeGenLoopConcatSystemData X A x0 hx0 n hn h2)
    (P : RelativeHomotopyGroupData X A x0 hx0 n hn h2 C)
    (R : RelativeHomotopyBoundaryRepresentativeSystemData hx0 n hn)
    (δ : RelativeHomotopyGroupCarrierData X A x0 hx0 n hn h2 P →
      HomotopyGroup (RelativeHomotopyBoundaryIndex n hn) A ⟨x0, hx0⟩) : Prop :=
  ∀ f : RelativeGenLoopData X A x0 n hn,
    δ (P.1.classOf
      (relativeHomotopyClassMkData f)) =
        relativeHomotopyBoundaryClassData hx0 R f

/-- Source-faithful relative homotopy boundary data on supplied group data. -/
abbrev RelativeHomotopyBoundaryData
    (X : Type u) [TopologicalSpace X] (A : Set X) (x0 : X)
    (hx0 : x0 ∈ A) (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    (C : RelativeGenLoopConcatSystemData X A x0 hx0 n hn h2)
    (P : RelativeHomotopyGroupData X A x0 hx0 n hn h2 C)
    (R : RelativeHomotopyBoundaryRepresentativeSystemData hx0 n hn) :=
  {δ :
      RelativeHomotopyGroupCarrierData X A x0 hx0 n hn h2 P →
        HomotopyGroup (RelativeHomotopyBoundaryIndex n hn) A ⟨x0, hx0⟩ //
    IsRelativeHomotopyBoundaryData X A x0 hx0 n hn h2 C P R δ}

/-- Source specification for the smaller cube used in Hatcher's relative
change-of-basepoint construction.  The distinguished zero face remains in the
corresponding outer face; the other coordinates are centered and halved. -/
def IsRelativeHomotopyBasepointInnerCubeData
    (n : ℕ) (hn : 0 < n)
    (e : (Fin n → unitInterval) → (Fin n → unitInterval)) : Prop :=
  ∀ t i,
    (e t i : ℝ) =
      if i = relativeHomotopyLastCoordinate n hn then
        (t i : ℝ) / 2
      else
        1 / 4 + (t i : ℝ) / 2

/-- Source-faithful coordinate placement data for Hatcher's smaller cube. -/
abbrev RelativeHomotopyBasepointInnerCubeData
    (n : ℕ) (hn : 0 < n) :=
  {e : (Fin n → unitInterval) → (Fin n → unitInterval) //
    IsRelativeHomotopyBasepointInnerCubeData n hn e}

/-- Exact construction-level specification for Hatcher's relative
change-of-basepoint representative `γf`.

The old representative `f` is placed in the centered half-size cube whose
distinguished face lies in the corresponding outer face.  Everywhere outside
that copy the new representative runs along the supplied path `γ` in `A`.
Hatcher leaves the radial reparametrization in the shell implicit in the
picture; the existential parameter function records precisely that harmless
choice without importing any homotopy or well-definedness result. -/
def IsRelativeHomotopyBasepointRepresentativeData
    {X : Type u} [TopologicalSpace X] {A : Set X}
    {x0 x1 : X} {hx0 : x0 ∈ A} {hx1 : x1 ∈ A}
    {n : ℕ} {hn : 0 < n}
    (e : RelativeHomotopyBasepointInnerCubeData n hn)
    (γ : Path (⟨x0, hx0⟩ : A) ⟨x1, hx1⟩)
    (f : RelativeGenLoopData X A x1 n hn)
    (g : RelativeGenLoopData X A x0 n hn) : Prop :=
  (∀ t, g.toContinuousMap (e.1 t) = f.toContinuousMap t) ∧
    ∃ ρ : (Fin n → unitInterval) → unitInterval,
      ∀ y, y ∉ Set.range e.1 → g.toContinuousMap y = (γ (ρ y) : A)

/-- Source-faithful relative change-of-basepoint representative data. -/
abbrev RelativeHomotopyBasepointRepresentativeData
    {X : Type u} [TopologicalSpace X] {A : Set X}
    {x0 x1 : X} (hx0 : x0 ∈ A) {hx1 : x1 ∈ A}
    {n : ℕ} {hn : 0 < n}
    (e : RelativeHomotopyBasepointInnerCubeData n hn)
    (γ : Path (⟨x0, hx0⟩ : A) ⟨x1, hx1⟩)
    (f : RelativeGenLoopData X A x1 n hn) :=
  {g : RelativeGenLoopData X A x0 n hn //
    IsRelativeHomotopyBasepointRepresentativeData e γ f g}

/-- Certified relative change-of-basepoint representatives for every source
relative cube. -/
structure RelativeHomotopyBasepointRepresentativeSystemData
    {X : Type u} [TopologicalSpace X] {A : Set X}
    {x0 x1 : X} (hx0 : x0 ∈ A) {hx1 : x1 ∈ A}
    (γ : Path (⟨x0, hx0⟩ : A) ⟨x1, hx1⟩)
    (n : ℕ) (hn : 0 < n) where
  innerCube : RelativeHomotopyBasepointInnerCubeData n hn
  representative : ∀ f : RelativeGenLoopData X A x1 n hn,
    RelativeHomotopyBasepointRepresentativeData hx0 innerCube γ f

/-- Exact source specification for relative change of basepoint on raw
homotopy classes. -/
def IsRelativeHomotopyBasepointClassMapData
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 x1 : X) (hx0 : x0 ∈ A) (hx1 : x1 ∈ A)
    (γ : Path (⟨x0, hx0⟩ : A) ⟨x1, hx1⟩)
    (n : ℕ) (hn : 0 < n)
    (D : RelativeHomotopyBasepointRepresentativeSystemData hx0 γ n hn)
    (β : RelativeHomotopyClassData X A x1 n hn →
      RelativeHomotopyClassData X A x0 n hn) : Prop :=
  ∀ f : RelativeGenLoopData X A x1 n hn,
    β (relativeHomotopyClassMkData f) =
      relativeHomotopyClassMkData
        (D.representative f).1

/-- Source-faithful relative change-of-basepoint data at the raw
homotopy-class level. -/
abbrev RelativeHomotopyBasepointClassMapData
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 x1 : X) (hx0 : x0 ∈ A) (hx1 : x1 ∈ A)
    (γ : Path (⟨x0, hx0⟩ : A) ⟨x1, hx1⟩)
    (n : ℕ) (hn : 0 < n)
    (D : RelativeHomotopyBasepointRepresentativeSystemData hx0 γ n hn) :=
  {β :
      RelativeHomotopyClassData X A x1 n hn →
        RelativeHomotopyClassData X A x0 n hn //
    IsRelativeHomotopyBasepointClassMapData X A x0 x1 hx0 hx1 γ n hn D β}

/-- Exact source specification for relative change of basepoint on the selected
group carriers in degree `n ≥ 2`.  The specification only records its action on
represented classes; being a group isomorphism is intentionally not a field. -/
def IsRelativeHomotopyBasepointData
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 x1 : X) (hx0 : x0 ∈ A) (hx1 : x1 ∈ A)
    (γ : Path (⟨x0, hx0⟩ : A) ⟨x1, hx1⟩)
    (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    (C0 : RelativeGenLoopConcatSystemData X A x0 hx0 n hn h2)
    (P0 : RelativeHomotopyGroupData X A x0 hx0 n hn h2 C0)
    (C1 : RelativeGenLoopConcatSystemData X A x1 hx1 n hn h2)
    (P1 : RelativeHomotopyGroupData X A x1 hx1 n hn h2 C1)
    (D : RelativeHomotopyBasepointRepresentativeSystemData hx0 γ n hn)
    (β : RelativeHomotopyGroupCarrierData X A x1 hx1 n hn h2 P1 →
      RelativeHomotopyGroupCarrierData X A x0 hx0 n hn h2 P0) : Prop :=
  ∀ f : RelativeGenLoopData X A x1 n hn,
    β (P1.1.classOf
      (relativeHomotopyClassMkData f)) =
        P0.1.classOf
          (relativeHomotopyClassMkData
            (D.representative f).1)

/-- Source-faithful relative change-of-basepoint data on supplied group
presentations. -/
abbrev RelativeHomotopyBasepointData
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 x1 : X) (hx0 : x0 ∈ A) (hx1 : x1 ∈ A)
    (γ : Path (⟨x0, hx0⟩ : A) ⟨x1, hx1⟩)
    (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n)
    (C0 : RelativeGenLoopConcatSystemData X A x0 hx0 n hn h2)
    (P0 : RelativeHomotopyGroupData X A x0 hx0 n hn h2 C0)
    (C1 : RelativeGenLoopConcatSystemData X A x1 hx1 n hn h2)
    (P1 : RelativeHomotopyGroupData X A x1 hx1 n hn h2 C1)
    (D : RelativeHomotopyBasepointRepresentativeSystemData hx0 γ n hn) :=
  {β :
      RelativeHomotopyGroupCarrierData X A x1 hx1 n hn h2 P1 →
        RelativeHomotopyGroupCarrierData X A x0 hx0 n hn h2 P0 //
    IsRelativeHomotopyBasepointData
      X A x0 x1 hx0 hx1 γ n hn h2 C0 P0 C1 P1 D β}

end LeanCategories.Topology
