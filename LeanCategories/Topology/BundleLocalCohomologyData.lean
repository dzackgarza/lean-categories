/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.BundleLocalHomologyData

/-!
# Cohomology with coefficients in a bundle of abelian groups

Definition-level realization of Hatcher FC07-C03-U156.

For a bundle of abelian groups `E → X`, Hatcher defines an `n`-cochain to
assign to every singular `n`-simplex `σ` a lift `φ(σ) : Δⁿ → E`.  The
coboundary is the ordinary alternating face formula after extending each face
lift over the whole simplex.  Relative cochains are the kernel of restriction
to simplices in the subspace.

Sweep III records the dependent product of lift groups, the exact
face-extension/coboundary graph, the cocycle and quotient presentations, and
the relative kernel construction.  It does not prove existence or uniqueness
of the face extensions, additivity of the displayed coboundary formula,
`δ² = 0`, preservation of relative cochains, or any quotient
well-definedness statement.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open CategoryTheory
open scoped BigOperators

universe u

/-- Hatcher's raw local-coefficient `n`-cochains: one lift for every
singular `n`-simplex. -/
abbrev LocalCoefficientRawCochainData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (n : ℕ) :=
  (σ : (localCoefficientSSet X).obj
    (Opposite.op (SimplexCategory.mk n))) →
      LocalCoefficientLiftData D σ

/-- Hatcher's cochain group `C^n(X;E)`, expressed as the dependent product
of the already routed groups of lifts of individual simplices. -/
abbrev LocalCoefficientCochainData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (n : ℕ) :=
  (σ : (localCoefficientSSet X).obj
    (Opposite.op (SimplexCategory.mk n))) →
      LocalCoefficientLiftGroupData D hD L σ

/-- Send a literal assignment of lifts to its pointwise classes in
`C^n(X;E)`. -/
def localCoefficientRawCochainClassData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    {n : ℕ} (φ : LocalCoefficientRawCochainData D n) :
    LocalCoefficientCochainData D hD L n :=
  fun σ => (L.group σ).1.classOf (φ σ)

/-- A lift of a face cochain extends over the ambient simplex when its
restriction to that face is the given lift.  Existence and uniqueness are
covering-space results and are not proved here. -/
def IsLocalCoefficientCofaceExtensionData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) {n : ℕ}
    {σ : (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))}
    (i : Fin (n + 2))
    (face : LocalCoefficientLiftData D ((localCoefficientSSet X).δ i σ))
    (extension : LocalCoefficientLiftData D σ) : Prop :=
  (localCoefficientSSet E).δ i extension.simplex = face.simplex

/-- Type of a candidate local-coefficient coboundary
`C^n(X;E) → C^{n+1}(X;E)`. -/
abbrev LocalCoefficientCoboundaryHomData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (n : ℕ) :=
  LocalCoefficientCochainData D hD L n →+
    LocalCoefficientCochainData D hD L (n + 1)

/-- Exact alternating-face/transport specification of Hatcher's coboundary.

For every raw cochain and every `(n+1)`-simplex, each face value is extended
to a lift of the whole simplex.  The output lift is the alternating pointwise
sum of these extensions. -/
def IsLocalCoefficientCoboundaryData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (n : ℕ) (d : LocalCoefficientCoboundaryHomData D hD L n) : Prop :=
  ∀ φ : LocalCoefficientRawCochainData D n,
    ∃ ψ : LocalCoefficientRawCochainData D (n + 1),
      (∀ σ : (localCoefficientSSet X).obj
          (Opposite.op (SimplexCategory.mk (n + 1))),
        ∃ extensions : ∀ i : Fin (n + 2), LocalCoefficientLiftData D σ,
          (∀ i,
            IsLocalCoefficientCofaceExtensionData D i
              (φ ((localCoefficientSSet X).δ i σ)) (extensions i)) ∧
          ∀ t : stdSimplex ℝ (Fin (n + 2)),
            localCoefficientLiftCoordinateData D (ψ σ) t =
              ∑ i : Fin (n + 2),
                (-1 : ℤ) ^ i.val •
                  localCoefficientLiftCoordinateData D (extensions i) t) ∧
      d (localCoefficientRawCochainClassData D hD L φ) =
        localCoefficientRawCochainClassData D hD L ψ

/-- Source-faithful local-coefficient coboundary data. -/
abbrev LocalCoefficientCoboundaryData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (n : ℕ) :=
  {d : LocalCoefficientCoboundaryHomData D hD L n //
    IsLocalCoefficientCoboundaryData D hD L n d}

/-- A certified coboundary in every degree. Square-zero is theorem content. -/
abbrev LocalCoefficientCoboundarySystemData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD) :=
  ∀ n : ℕ, LocalCoefficientCoboundaryData D hD L n

/-- Local-coefficient cocycles in degree `n`. -/
def IsLocalCoefficientCocycleData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (n : ℕ) (x : LocalCoefficientCochainData D hD L n) : Prop :=
  (C n).1 x = 0

/-- A local-coefficient cocycle, without installing a subgroup structure. -/
structure LocalCoefficientCocycleData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (n : ℕ) where
  cochain : LocalCoefficientCochainData D hD L n
  isCocycle : IsLocalCoefficientCocycleData D hD L C n cochain

/-- Difference of two degree-`n` cocycles is a coboundary.  In degree zero
there are no negative-degree cochains. -/
def IsLocalCoefficientCoboundaryDifferenceData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (n : ℕ) (x y : LocalCoefficientCochainData D hD L n) : Prop :=
  match n with
  | 0 => x = y
  | m + 1 =>
      ∃ z : LocalCoefficientCochainData D hD L m,
        x - y = (C m).1 z

/-- Candidate quotient carrier for `H^n(X;E)`. -/
structure LocalCoefficientCohomologyCandidateData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (n : ℕ) where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  classOf : LocalCoefficientCocycleData D hD L C n → carrier

attribute [instance] LocalCoefficientCohomologyCandidateData.instAddCommGroup

/-- Exact cocycles-mod-coboundaries specification of `H^n(X;E)`.

No claim that coboundaries are cocycles or that the displayed relation is an
equivalence relation is proved in Sweep III. -/
def IsLocalCoefficientCohomologyData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (n : ℕ) (H : LocalCoefficientCohomologyCandidateData D hD L C n) : Prop :=
  Function.Surjective H.classOf ∧
    (∀ x y,
      H.classOf x = H.classOf y ↔
        IsLocalCoefficientCoboundaryDifferenceData D hD L C n x.cochain y.cochain) ∧
    (∃ z : LocalCoefficientCocycleData D hD L C n,
      z.cochain = 0 ∧ H.classOf z = 0) ∧
    ∀ x y : LocalCoefficientCocycleData D hD L C n,
      ∃ z : LocalCoefficientCocycleData D hD L C n,
        z.cochain = x.cochain + y.cochain ∧
          H.classOf z = H.classOf x + H.classOf y

/-- Source-faithful `H^n(X;E)` quotient presentation data. -/
abbrev LocalCoefficientCohomologyData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (n : ℕ) :=
  {H : LocalCoefficientCohomologyCandidateData D hD L C n //
    IsLocalCoefficientCohomologyData D hD L C n H}

/-- Source-facing carrier of cohomology with coefficients in the bundle
`E`. -/
abbrev LocalCoefficientCohomologyGroupData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    {L : LocalCoefficientLiftGroupSystemData D hD}
    {C : LocalCoefficientCoboundarySystemData D hD L}
    {n : ℕ} (H : LocalCoefficientCohomologyData D hD L C n) : Type u :=
  H.1.carrier

/-- Regard a singular simplex in a subspace `A ⊆ X` as a singular simplex
of `X`. -/
def localCoefficientSubsetSimplexData
    {X : Type u} [TopologicalSpace X] (A : Set X) {n : ℕ}
    (σ : (localCoefficientSSet A).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (localCoefficientSSet X).obj
      (Opposite.op (SimplexCategory.mk n)) :=
  (TopCat.toSSet.map
      (TopCat.ofHom
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))).app
    (Opposite.op (SimplexCategory.mk n)) σ

/-- Raw relative cochains are precisely raw cochains vanishing on every
singular simplex contained in `A`; this is Hatcher's kernel-of-restriction
description. -/
def IsLocalCoefficientRelativeRawCochainData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (A : Set X) {n : ℕ}
    (φ : LocalCoefficientRawCochainData D n) : Prop :=
  ∀ σ : (localCoefficientSSet A).obj
      (Opposite.op (SimplexCategory.mk n)),
    IsZeroLocalCoefficientLiftData D
      (φ (localCoefficientSubsetSimplexData A σ))

/-- A raw relative cochain together with the literal vanishing condition on
`A`. -/
structure LocalCoefficientRelativeRawCochainData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (A : Set X) (n : ℕ) where
  cochain : LocalCoefficientRawCochainData D n
  isRelative : IsLocalCoefficientRelativeRawCochainData D A cochain

/-- Candidate abelian group of relative cochains, with its inclusion into the
absolute cochain group. -/
structure LocalCoefficientRelativeCochainCandidateData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (A : Set X) (n : ℕ) where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  classOf : LocalCoefficientRelativeRawCochainData D A n → carrier
  toAbsolute : carrier →+ LocalCoefficientCochainData D hD L n

attribute [instance]
  LocalCoefficientRelativeCochainCandidateData.instAddCommGroup

/-- Exact kernel-of-restriction specification for relative cochains. -/
def IsLocalCoefficientRelativeCochainData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (A : Set X) (n : ℕ)
    (P : LocalCoefficientRelativeCochainCandidateData D hD L A n) : Prop :=
  Function.Bijective P.classOf ∧
    Function.Injective P.toAbsolute ∧
    ∀ φ : LocalCoefficientRelativeRawCochainData D A n,
      P.toAbsolute (P.classOf φ) =
        localCoefficientRawCochainClassData D hD L φ.cochain

/-- Source-faithful relative cochain presentation data. -/
abbrev LocalCoefficientRelativeCochainData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (A : Set X) (n : ℕ) :=
  {P : LocalCoefficientRelativeCochainCandidateData D hD L A n //
    IsLocalCoefficientRelativeCochainData D hD L A n P}

/-- A certified relative cochain presentation in every degree. -/
abbrev LocalCoefficientRelativeCochainSystemData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (A : Set X) :=
  ∀ n : ℕ, LocalCoefficientRelativeCochainData D hD L A n

/-- Source-facing relative cochain group `C^n(X,A;E)`. -/
abbrev LocalCoefficientRelativeCochainGroupData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    {L : LocalCoefficientLiftGroupSystemData D hD}
    {A : Set X} (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (n : ℕ) : Type u :=
  (R n).1.carrier

/-- Type of a candidate relative local-coefficient coboundary. -/
abbrev LocalCoefficientRelativeCoboundaryHomData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    {A : Set X} (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (n : ℕ) :=
  LocalCoefficientRelativeCochainGroupData D hD R n →+
    LocalCoefficientRelativeCochainGroupData D hD R (n + 1)

/-- The relative coboundary is exactly the restriction of the absolute
coboundary to the relative kernel.  Preservation of the kernel is not proved
here. -/
def IsLocalCoefficientRelativeCoboundaryData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (n : ℕ)
    (d : LocalCoefficientRelativeCoboundaryHomData D hD L R n) : Prop :=
  ∀ x,
    (R (n + 1)).1.toAbsolute (d x) =
      (C n).1 ((R n).1.toAbsolute x)

/-- Source-faithful relative coboundary data. -/
abbrev LocalCoefficientRelativeCoboundaryData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (n : ℕ) :=
  {d : LocalCoefficientRelativeCoboundaryHomData D hD L R n //
    IsLocalCoefficientRelativeCoboundaryData D hD L C A R n d}

/-- A certified relative coboundary in every degree. -/
abbrev LocalCoefficientRelativeCoboundarySystemData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A) :=
  ∀ n : ℕ, LocalCoefficientRelativeCoboundaryData D hD L C A R n

/-- Relative local-coefficient cocycles. -/
def IsLocalCoefficientRelativeCocycleData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (RC : LocalCoefficientRelativeCoboundarySystemData D hD L C A R)
    (n : ℕ)
    (x : LocalCoefficientRelativeCochainGroupData D hD R n) : Prop :=
  (RC n).1 x = 0

/-- A relative local-coefficient cocycle. -/
structure LocalCoefficientRelativeCocycleData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (RC : LocalCoefficientRelativeCoboundarySystemData D hD L C A R)
    (n : ℕ) where
  cochain : LocalCoefficientRelativeCochainGroupData D hD R n
  isCocycle : IsLocalCoefficientRelativeCocycleData D hD L C A R RC n cochain

/-- Relative cocycles differ by a relative coboundary. -/
def IsLocalCoefficientRelativeCoboundaryDifferenceData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (RC : LocalCoefficientRelativeCoboundarySystemData D hD L C A R)
    (n : ℕ)
    (x y : LocalCoefficientRelativeCochainGroupData D hD R n) : Prop :=
  match n with
  | 0 => x = y
  | m + 1 =>
      ∃ z : LocalCoefficientRelativeCochainGroupData D hD R m,
        x - y = (RC m).1 z

/-- Candidate quotient carrier for `H^n(X,A;E)`. -/
structure LocalCoefficientRelativeCohomologyCandidateData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (RC : LocalCoefficientRelativeCoboundarySystemData D hD L C A R)
    (n : ℕ) where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  classOf : LocalCoefficientRelativeCocycleData D hD L C A R RC n → carrier

attribute [instance]
  LocalCoefficientRelativeCohomologyCandidateData.instAddCommGroup

/-- Exact quotient specification for relative local-coefficient cohomology. -/
def IsLocalCoefficientRelativeCohomologyData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (RC : LocalCoefficientRelativeCoboundarySystemData D hD L C A R)
    (n : ℕ)
    (H : LocalCoefficientRelativeCohomologyCandidateData D hD L C A R RC n) : Prop :=
  Function.Surjective H.classOf ∧
    (∀ x y,
      H.classOf x = H.classOf y ↔
        IsLocalCoefficientRelativeCoboundaryDifferenceData
          D hD L C A R RC n x.cochain y.cochain) ∧
    (∃ z : LocalCoefficientRelativeCocycleData D hD L C A R RC n,
      z.cochain = 0 ∧ H.classOf z = 0) ∧
    ∀ x y : LocalCoefficientRelativeCocycleData D hD L C A R RC n,
      ∃ z : LocalCoefficientRelativeCocycleData D hD L C A R RC n,
        z.cochain = x.cochain + y.cochain ∧
          H.classOf z = H.classOf x + H.classOf y

/-- Source-faithful relative local-coefficient cohomology quotient data. -/
abbrev LocalCoefficientRelativeCohomologyData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    (L : LocalCoefficientLiftGroupSystemData D hD)
    (C : LocalCoefficientCoboundarySystemData D hD L)
    (A : Set X) (R : LocalCoefficientRelativeCochainSystemData D hD L A)
    (RC : LocalCoefficientRelativeCoboundarySystemData D hD L C A R)
    (n : ℕ) :=
  {H : LocalCoefficientRelativeCohomologyCandidateData D hD L C A R RC n //
    IsLocalCoefficientRelativeCohomologyData D hD L C A R RC n H}

/-- Source-facing carrier of `H^n(X,A;E)`. -/
abbrev LocalCoefficientRelativeCohomologyGroupData
    {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    (D : AbelianGroupBundleData E X) (hD : IsAbelianGroupBundleData D)
    {L : LocalCoefficientLiftGroupSystemData D hD}
    {C : LocalCoefficientCoboundarySystemData D hD L}
    {A : Set X} {R : LocalCoefficientRelativeCochainSystemData D hD L A}
    {RC : LocalCoefficientRelativeCoboundarySystemData D hD L C A R}
    {n : ℕ} (H : LocalCoefficientRelativeCohomologyData D hD L C A R RC n) : Type u :=
  H.1.carrier

end LeanCategories.Topology
