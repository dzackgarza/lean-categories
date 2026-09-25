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

noncomputable def cartanLerayCochainRepresentationData
    (a : CartanLerayActionData G X) (q : ℕ) :
    CartanLerayCochainRepresentationCandidateData G X q :=
  Classical.epsilon (IsCartanLerayCochainRepresentationData a q)

noncomputable abbrev cartanLerayCochainRepData
    (a : CartanLerayActionData G X) (q : ℕ) : Rep ℤ G :=
  Rep.of (cartanLerayCochainRepresentationData a q)

def IsCartanLerayCoefficientComplexData
    (a : CartanLerayActionData G X)
    (K : CochainComplex (Rep ℤ G) ℕ) : Prop :=
  ∃ e : ∀ q : ℕ, K.X q ≅ cartanLerayCochainRepData a q,
    ∀ q : ℕ,
      ((e q).inv ≫ K.d q (q + 1) ≫ (e (q + 1)).hom).hom.toLinearMap =
        ((LeanCategories.Topology.singularCochainComplexData
          ℤ (TopCat.of X) (ModuleCat.of ℤ ℤ)).d q (q + 1)).hom

noncomputable def cartanLerayCoefficientComplexData
    (a : CartanLerayActionData G X) :
    CochainComplex (Rep ℤ G) ℕ :=
  Classical.epsilon (IsCartanLerayCoefficientComplexData a)

noncomputable def cartanLerayDoubleComplexData
    (a : CartanLerayActionData G X) :
    CochainComplex (CochainComplex (ModuleCat ℤ) ℕ) ℕ :=
  ((groupCohomology.cochainsFunctor ℤ G).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (cartanLerayCoefficientComplexData a)

def IsFreeCartanLerayActionData (a : CartanLerayActionData G X) : Prop :=
  ∀ g : G, g ≠ 1 → ∀ x : X, a g x ≠ x

end LeanCategories.Homological
