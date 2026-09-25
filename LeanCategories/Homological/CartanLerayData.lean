module

public import LeanCategories.Topology.CohomologyCrossProductData
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Cartan--Leray double-complex data

Definition-level support for Peters--Sterk FC11-A-U052.

For a group acting on a space by homeomorphisms, Cartan--Leray applies group
cochains to the singular cochain complex. Since singular cochains are
contravariant, g acts by pullback along g inverse.

This file records the exact coefficient representation complex and the
resulting first-quadrant double complex. It does not prove equivariance of the
singular coboundary, identify the second page, compare the total complex with
the quotient, or prove convergence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology

namespace LeanCategories.Homological

variable {G X : Type} [Group G] [TopologicalSpace X]

abbrev CartanLerayActionData (G X : Type) [Group G] [TopologicalSpace X] :=
  G →* (X ≃ₜ X)

noncomputable abbrev cartanLeraySingularCochainData
    (X : Type) [TopologicalSpace X] (q : ℕ) :=
  (LeanCategories.Topology.singularCochainComplexData
    ℤ (TopCat.of X) (ModuleCat.of ℤ ℤ)).X q

abbrev CartanLerayCochainRepresentationCandidateData
    (G X : Type) [Group G] [TopologicalSpace X] (q : ℕ) :=
  Representation ℤ G (cartanLeraySingularCochainData X q)

def IsCartanLerayCochainRepresentationData
    (a : CartanLerayActionData G X) (q : ℕ)
    (ρ : CartanLerayCochainRepresentationCandidateData G X q) : Prop :=
  ∀ g : G,
    ρ g =
      ((LeanCategories.Topology.singularCochainMapData ℤ
        (TopCat.ofHom ⟨a g⁻¹, (a g⁻¹).continuous⟩)).f q).hom

/-- Regard supplied degree-`q` action data as a representation object.  The
separate exact predicate records whether it is the pullback action required by
Cartan--Leray. -/
noncomputable abbrev cartanLerayCochainRepData
    {q : ℕ} (ρ : CartanLerayCochainRepresentationCandidateData G X q) : Rep ℤ G :=
  Rep.of ρ

/-- Proof-free presentation of the coefficient complex used by Cartan--Leray.
The representation family and the complex are data; source-faithfulness is
recorded separately by `IsCartanLerayCoefficientComplexData`. -/
structure CartanLerayCoefficientComplexPresentationData
    (G X : Type) [Group G] [TopologicalSpace X] where
  representation : ∀ q : ℕ, CartanLerayCochainRepresentationCandidateData G X q
  complex : CochainComplex (Rep ℤ G) ℕ

/-- Exact graph specifying that a supplied coefficient-complex presentation is
the singular cochain complex with the inverse-pullback `G`-action. -/
def IsCartanLerayCoefficientComplexData
    (a : CartanLerayActionData G X)
    (D : CartanLerayCoefficientComplexPresentationData G X) : Prop :=
  (∀ q : ℕ, IsCartanLerayCochainRepresentationData a q (D.representation q)) ∧
  ∃ e : ∀ q : ℕ, D.complex.X q ≅ cartanLerayCochainRepData (D.representation q),
    ∀ q : ℕ,
      ((e q).inv ≫ D.complex.d q (q + 1) ≫ (e (q + 1)).hom).hom.toLinearMap =
        ((LeanCategories.Topology.singularCochainComplexData
          ℤ (TopCat.of X) (ModuleCat.of ℤ ℤ)).d q (q + 1)).hom

/-- Apply group cochains degreewise to a supplied Cartan--Leray coefficient
complex presentation.  No claim that the supplied presentation satisfies its
exact graph is made here. -/
noncomputable def cartanLerayDoubleComplexData
    (D : CartanLerayCoefficientComplexPresentationData G X) :
    CochainComplex (CochainComplex (ModuleCat ℤ) ℕ) ℕ :=
  ((groupCohomology.cochainsFunctor ℤ G).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj D.complex

def IsFreeCartanLerayActionData (a : CartanLerayActionData G X) : Prop :=
  ∀ g : G, g ≠ 1 → ∀ x : X, a g x ≠ x

end LeanCategories.Homological
