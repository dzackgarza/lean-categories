module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Modules.Expressions
public import LeanCategories.Modules.Mathlib
public import LeanCategories.Modules.Framed
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Modules.Expressions
public meta import LeanCategories.Modules.Catalogue

@[expose] public section

namespace LeanCategories.Modules.CatalogueRegistration

open CategoryTheory
open LeanCategories

universe u

noncomputable def modulesFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u, u} CategoryFamilyId.modules .ring where
  transport := Modules.Mathlib.moduleCatRestrictScalarsPseudofunctor
  transportSemantics := .restrictionOfScalars
noncomputable def modulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.Modules (modulesFamilyRealization.fibre R) where
  familyFibre := some (.mk modulesFamilyRealization {
    parameter := R
    parameterQuotation := .ringR R
    category_eq := by rfl })

noncomputable def genFrameFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (GenFrame parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def genFrameFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u, u + 1}
      CategoryFamilyId.genFrame .commRingNat where
  transport := genFrameFamilyTransport
  transportSemantics := .discrete

noncomputable def basisFrameFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (BasisFrame parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def basisFrameFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u, u + 1}
      CategoryFamilyId.basisFrame .commRingNat where
  transport := basisFrameFamilyTransport
  transportSemantics := .discrete

noncomputable def coordFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (Coord parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def coordFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u, u + 1}
      CategoryFamilyId.coord .commRingNat where
  transport := coordFamilyTransport
  transportSemantics := .discrete

noncomputable def genFrameCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (GenFrame R (Fin n))

noncomputable def basisFrameCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (BasisFrame R (Fin n))

noncomputable def coordCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (Coord R (Fin n))

noncomputable def genFrameRealization (R : Type u) [CommRing R] (n : Nat) :
    CategoryRealization Modules.GenFrameExpr (genFrameCategory R n) where
  familyFibre := some (.mk genFrameFamilyRealization {
    parameter := ⟨CommRingCat.of R, n⟩
    parameterQuotation := .commRingNat (CommRingCat.of R) n
    category_eq := by rfl })

noncomputable def basisFrameRealization (R : Type u) [CommRing R] (n : Nat) :
    CategoryRealization Modules.BasisFrameExpr (basisFrameCategory R n) where
  familyFibre := some (.mk basisFrameFamilyRealization {
    parameter := ⟨CommRingCat.of R, n⟩
    parameterQuotation := .commRingNat (CommRingCat.of R) n
    category_eq := by rfl })

noncomputable def coordRealization (R : Type u) [CommRing R] (n : Nat) :
    CategoryRealization Modules.CoordExpr (coordCategory R n) where
  familyFibre := some (.mk coordFamilyRealization {
    parameter := ⟨CommRingCat.of R, n⟩
    parameterQuotation := .commRingNat (CommRingCat.of R) n
    category_eq := by rfl })
noncomputable def freeModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FreeModules (Modules.Mathlib.free R).total :=
  { familyFibre := none }
noncomputable def finitelyGeneratedModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FinitelyGeneratedModules
      (Modules.Mathlib.finitelyGenerated R).total := { familyFibre := none }
noncomputable def finiteRankModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FiniteRankModules
      (Modules.Mathlib.finiteRank R).total := { familyFibre := none }

noncomputable def basisFrameToGenFrameRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization Modules.BasisFrameToGenFrameExpr
      (basisFrameCategory R n) (genFrameCategory R n)
      (basisFrameToGenFrame R (Fin n)).toCatHom :=
  { sourceRealization := basisFrameRealization R n
    targetRealization := genFrameRealization R n }

noncomputable def fromBasisFrameRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization Modules.FromBasisFrameExpr
      (basisFrameCategory R n) (coordCategory R n)
      (Coord.fromBasisFrame R (Fin n)).toCatHom :=
  { sourceRealization := basisFrameRealization R n
    targetRealization := coordRealization R n }

noncomputable def coordForgetRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization Modules.CoordForgetExpr
      (coordCategory R n) (Modules.Mathlib.ModulesOf (RingCat.of R))
      (Coord.forget R (Fin n)).toCatHom :=
  { sourceRealization := coordRealization R n
    targetRealization := modulesRealization (RingCat.of R) }

noncomputable def basisFrameToGenFrameDeclaration (R : Type u) [CommRing R] (n : Nat) :
    basisFrameCategory R n ⟶ genFrameCategory R n :=
  (basisFrameToGenFrame R (Fin n)).toCatHom

noncomputable def fromBasisFrameDeclaration (R : Type u) [CommRing R] (n : Nat) :
    basisFrameCategory R n ⟶ coordCategory R n :=
  (Coord.fromBasisFrame R (Fin n)).toCatHom

noncomputable def coordForgetDeclaration (R : Type u) [CommRing R] (n : Nat) :
    coordCategory R n ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (Coord.forget R (Fin n)).toCatHom

noncomputable def freeRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFree
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.free R) :=
  { hostRealization := modulesRealization R, totalRealization := {} }
noncomputable def finitelyGeneratedRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFinitelyGenerated
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.finitelyGenerated R) :=
  { hostRealization := modulesRealization R, totalRealization := {} }
noncomputable def finiteRankRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFiniteRank
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.finiteRank R) :=
  { hostRealization := modulesRealization R, totalRealization := {} }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.modules, canonicalName := "Modules"
    schema := .ring
    realization := `LeanCategories.Modules.CatalogueRegistration.modulesFamilyRealization
    transport := `LeanCategories.Modules.Mathlib.moduleCatRestrictScalarsPseudofunctor
    transportSemantics := .restrictionOfScalars }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.genFrame, canonicalName := "GenFrame(R, n)"
    schema := .commRingNat
    realization := `LeanCategories.Modules.CatalogueRegistration.genFrameFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.genFrameFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.basisFrame, canonicalName := "BasisFrame(R, n)"
    schema := .commRingNat
    realization := `LeanCategories.Modules.CatalogueRegistration.basisFrameFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.basisFrameFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.coord, canonicalName := "Coord(R, n)"
    schema := .commRingNat
    realization := `LeanCategories.Modules.CatalogueRegistration.coordFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.coordFamilyTransport
    transportSemantics := .discrete }

normalized_registry .classifier
  { id := ClassifierId.modulesFree, canonicalName := "Free"
    declaration := `LeanCategories.Modules.Mathlib.free
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.freeRealization}
normalized_registry .classifier
  { id := ClassifierId.modulesFinitelyGenerated, canonicalName := "FinitelyGenerated"
    declaration := `LeanCategories.Modules.Mathlib.finitelyGenerated
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.finitelyGeneratedRealization}
normalized_registry .classifier
  { id := ClassifierId.modulesFiniteRank, canonicalName := "FiniteRank"
    declaration := `LeanCategories.Modules.Mathlib.finiteRank
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.finiteRankRealization}

normalized_registry .category
  { id := CategoryId.modulesR, canonicalName := "Modules(R)"
    declaration := `LeanCategories.Modules.Mathlib.ModulesOf
    expression := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.modulesRealization}
normalized_registry .category
  { id := CategoryId.freeModules, canonicalName := "FreeModules(R)"
    declaration := `LeanCategories.Modules.Mathlib.FreeModules
    expression := Modules.FreeModules
    realization := `LeanCategories.Modules.CatalogueRegistration.freeModulesRealization}
normalized_registry .category
  { id := CategoryId.finitelyGeneratedModules
    canonicalName := "FinitelyGeneratedModules(R)"
    declaration := `LeanCategories.Modules.Mathlib.FinitelyGeneratedModules
    expression := Modules.FinitelyGeneratedModules
    realization := `LeanCategories.Modules.CatalogueRegistration.finitelyGeneratedModulesRealization}
normalized_registry .category
  { id := CategoryId.finiteRankModules, canonicalName := "FiniteRankModules(R)"
    declaration := `LeanCategories.Modules.Mathlib.FiniteRankModules
    expression := Modules.FiniteRankModules
    realization := `LeanCategories.Modules.CatalogueRegistration.finiteRankModulesRealization}

normalized_registry .category
  { id := CategoryId.genFrame, canonicalName := "GenFrame"
    declaration := `LeanCategories.Modules.CatalogueRegistration.genFrameCategory
    expression := Modules.GenFrameExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.genFrameRealization }
normalized_registry .category
  { id := CategoryId.basisFrame, canonicalName := "BasisFrame"
    declaration := `LeanCategories.Modules.CatalogueRegistration.basisFrameCategory
    expression := Modules.BasisFrameExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.basisFrameRealization }
normalized_registry .category
  { id := CategoryId.coord, canonicalName := "Coord"
    declaration := `LeanCategories.Modules.CatalogueRegistration.coordCategory
    expression := Modules.CoordExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.coordRealization }

normalized_registry .functor
  { id := FunctorId.basisFrameToGenFrame, canonicalName := "BasisFrame.toGenFrame"
    source := Modules.BasisFrameExpr
    target := Modules.GenFrameExpr
    declaration := `LeanCategories.Modules.CatalogueRegistration.basisFrameToGenFrameDeclaration
    realization :=
      `LeanCategories.Modules.CatalogueRegistration.basisFrameToGenFrameRealization
    expression := Modules.BasisFrameToGenFrameExpr }
normalized_registry .functor
  { id := FunctorId.fromBasisFrame, canonicalName := "Coord.fromBasisFrame"
    source := Modules.BasisFrameExpr
    target := Modules.CoordExpr
    declaration := `LeanCategories.Modules.CatalogueRegistration.fromBasisFrameDeclaration
    realization := `LeanCategories.Modules.CatalogueRegistration.fromBasisFrameRealization
    expression := Modules.FromBasisFrameExpr }
normalized_registry .functor
  { id := FunctorId.coordForget, canonicalName := "Coord.forget"
    source := Modules.CoordExpr
    target := Modules.Modules
    declaration := `LeanCategories.Modules.CatalogueRegistration.coordForgetDeclaration
    realization := `LeanCategories.Modules.CatalogueRegistration.coordForgetRealization
    expression := Modules.CoordForgetExpr }

end LeanCategories.Modules.CatalogueRegistration
