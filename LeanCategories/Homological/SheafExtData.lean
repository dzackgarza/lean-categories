/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Global Ext and sheaf Ext data

Definition-level realization of Hartshorne FC06-C03-U065.

Mathlib already provides global Ext in an abelian category.  The current pin
does not package the `𝒪_X`-linear internal-Hom functor on `X.Modules`, and it
does not provide `HasInjectiveResolutions X.Modules`.  This file therefore
records the exact local-section specification of the missing internal-Hom
functor and the standard resolution-level definition of sheaf Ext.

Existence of an internal-Hom object satisfying this specification, existence
of injective resolutions in `X.Modules`, and independence of the chosen
resolution are result-layer statements and are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace LeanCategories.Homological

universe u

variable {X : Scheme.{u}}

/-- Restrict an `𝒪_X`-module first to `U` and then to `V ⊆ U`, identified with
its direct restriction to `V`. -/
def moduleRestrictRestrictIso (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    (M.restrict U.ι).restrict (X.homOfLE h) ≅ M.restrict V.ι :=
  ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M).symm ≪≫
    ((Scheme.Modules.restrictFunctorCongr (by simp)).app M)

/-- Restriction of a morphism between module sheaves on an open set. -/
def restrictModuleHom {F G : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    F.restrict V.ι ⟶ G.restrict V.ι :=
  (moduleRestrictRestrictIso F h).inv ≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map φ ≫
    (moduleRestrictRestrictIso G h).hom

/-- Presentation data for the internal sheaf-Hom from `F` to `G`.

Sections on `U` are additively identified with `𝒪_U`-linear morphisms
`F|_U ⟶ G|_U`; the remaining fields state compatibility with restriction and
with the canonical pointwise action of `Γ(X,U)`.  These are specification
fields, not proofs constructed in Sweep III. -/
structure InternalHomPresentationData (F G H : X.Modules) where
  sectionEquiv (U : X.Opens) : Γ(H, U) ≃+ (F.restrict U.ι ⟶ G.restrict U.ι)
  restrict_compat {U V : X.Opens} (h : V ≤ U) (s : Γ(H, U)) :
    sectionEquiv V (H.presheaf.map (.op (homOfLE h)) s) =
      restrictModuleHom h (sectionEquiv U s)
  smulHom (U : X.Opens) (r : Γ(X, U)) :
    (F.restrict U.ι ⟶ G.restrict U.ι) →
      (F.restrict U.ι ⟶ G.restrict U.ι)
  smul_compat (U : X.Opens) (r : Γ(X, U)) (s : Γ(H, U)) :
    sectionEquiv U (r • s) = smulHom U r (sectionEquiv U s)
  smulHom_app (U : X.Opens) (r : Γ(X, U))
      (φ : F.restrict U.ι ⟶ G.restrict U.ι) (W : (U : Scheme).Opens) :
    (smulHom U r φ).app W =
      φ.app W ≫ (G.restrict U.ι).smul
        ((U : Scheme).presheaf.map (.op (homOfLE le_top)) (U.topIso.inv r))

/-- A functorial internal-Hom candidate for a fixed source module sheaf `F`,
together with the local-section specification above. -/
structure InternalHomFunctorData (F : X.Modules) where
  functor : X.Modules ⥤ X.Modules
  additive : functor.Additive
  presentation (G : X.Modules) :
    InternalHomPresentationData F G (functor.obj G)

/-- Hartshorne's global Ext, using Mathlib's native Ext object whenever the
ambient abelian category has the corresponding derived-category smallness
data. -/
abbrev moduleSheafGlobalExt [HasExt X.Modules]
    (F G : X.Modules) (i : ℕ) := CategoryTheory.Abelian.Ext F G i

/-- Hartshorne's sheaf Ext object computed from a specified internal-Hom
functor and a chosen injective resolution of the second argument.

Independence of `I` and the existence of suitable `D` and `I` are theorem
content, not part of this definition. -/
def sheafExtFromResolution (F : X.Modules)
    (D : InternalHomFunctorData F) {G : X.Modules}
    (I : InjectiveResolution G) (i : ℕ) : X.Modules := by
  letI := D.additive
  exact ((D.functor.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology i

end LeanCategories.Homological
