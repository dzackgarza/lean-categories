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

noncomputable section

open CategoryTheory
open LeanCategories

universe u
universe v
universe w

noncomputable def modulesFamilyRealization :
    CategoryFamilyRealization.{max u (w + 1), w, u, u + 1}
      CategoryFamilyId.modules .ring (P := RingCat.{u}) where
  transport := Modules.Mathlib.moduleCatRestrictScalarsPseudofunctor.{u, w}
  transportSemantics := .restrictionOfScalars
noncomputable def modulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.Modules (Modules.Mathlib.ModulesOf.{u, w} R) where
  familyFibre := some (.mk (modulesFamilyRealization.{u, w}) {
    parameter := R
    parameterQuotation := .ringR R
    category_eq := by rfl })

noncomputable def genFrameFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete (Discrete (Σ _R : CommRingCat.{u}, Nat))ᵒᵖ)
      (Cat.{u, u + 1}) :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (GenFrame parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def genFrameFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.genFrame .commRingNat
      (P := Discrete (Σ _R : CommRingCat.{u}, Nat)) where
  transport := genFrameFamilyTransport
  transportSemantics := .discrete

noncomputable def basisFrameFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete (Discrete (Σ _R : CommRingCat.{u}, Nat))ᵒᵖ)
      (Cat.{u, u + 1}) :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (BasisFrame parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def basisFrameFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.basisFrame .commRingNat
      (P := Discrete (Σ _R : CommRingCat.{u}, Nat)) where
  transport := basisFrameFamilyTransport
  transportSemantics := .discrete

noncomputable def coordFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete (Discrete (Σ _R : CommRingCat.{u}, Nat))ᵒᵖ)
      (Cat.{u, u + 1}) :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (Coord parameter.1 (Fin parameter.2)) : ObjCat.{u + 1, u}))

noncomputable def coordFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.coord .commRingNat
      (P := Discrete (Σ _R : CommRingCat.{u}, Nat)) where
  transport := coordFamilyTransport
  transportSemantics := .discrete

noncomputable def genFrameIndexedFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ _R : CommRingCat.{u}, Type v))ᵒᵖ)
      (Cat.{max u v, max (u + 1) (v + 1)}) :=
  discreteFamilyTransport.{max (u + 1) (v + 1), max u v, max (u + 1) (v + 1)}
    (P := Σ _R : CommRingCat.{u}, Type v)
    (fun parameter =>
      letI := parameter.1.commRing
      Cat.of (GenFrame parameter.1 parameter.2))

noncomputable def genFrameIndexedFamilyRealization :
    CategoryFamilyRealization.{max (u + 1) (v + 1), max u v,
      max (u + 1) (v + 1), max (u + 1) (v + 1)}
      CategoryFamilyId.genFrameIndexed .commRingIndexType
      (P := Discrete (Σ _R : CommRingCat.{u}, Type v)) where
  transport := genFrameIndexedFamilyTransport
  transportSemantics := .discrete

noncomputable def basisFrameIndexedFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ _R : CommRingCat.{u}, Type v))ᵒᵖ)
      (Cat.{max u v, max (u + 1) (v + 1)}) :=
  discreteFamilyTransport.{max (u + 1) (v + 1), max u v, max (u + 1) (v + 1)}
    (P := Σ _R : CommRingCat.{u}, Type v)
    (fun parameter =>
      letI := parameter.1.commRing
      Cat.of (BasisFrame parameter.1 parameter.2))

noncomputable def basisFrameIndexedFamilyRealization :
    CategoryFamilyRealization.{max (u + 1) (v + 1), max u v,
      max (u + 1) (v + 1), max (u + 1) (v + 1)}
      CategoryFamilyId.basisFrameIndexed .commRingIndexType
      (P := Discrete (Σ _R : CommRingCat.{u}, Type v)) where
  transport := basisFrameIndexedFamilyTransport
  transportSemantics := .discrete

noncomputable def coordIndexedFamilyTransport :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ _R : CommRingCat.{u}, Type v))ᵒᵖ)
      (Cat.{max u v, max (u + 1) (v + 1)}) :=
  discreteFamilyTransport.{max (u + 1) (v + 1), max u v, max (u + 1) (v + 1)}
    (P := Σ _R : CommRingCat.{u}, Type v)
    (fun parameter =>
      letI := parameter.1.commRing
      Cat.of (Coord parameter.1 parameter.2))

noncomputable def coordIndexedFamilyRealization :
    CategoryFamilyRealization.{max (u + 1) (v + 1), max u v,
      max (u + 1) (v + 1), max (u + 1) (v + 1)}
      CategoryFamilyId.coordIndexed .commRingIndexType
      (P := Discrete (Σ _R : CommRingCat.{u}, Type v)) where
  transport := coordIndexedFamilyTransport
  transportSemantics := .discrete

noncomputable def genFrameCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (GenFrame R (Fin n))

noncomputable def basisFrameCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (BasisFrame R (Fin n))

noncomputable def coordCategory (R : Type u) [CommRing R] (n : Nat) : ObjCat.{u + 1, u} :=
  Cat.of (Coord R (Fin n))

noncomputable def genFrameIndexedCategory (R : Type u) [CommRing R] (I : Type v) :
    ObjCat.{max (u + 1) (v + 1), max u v} :=
  Cat.of (GenFrame R I)

noncomputable def basisFrameIndexedCategory (R : Type u) [CommRing R] (I : Type v) :
    ObjCat.{max (u + 1) (v + 1), max u v} :=
  Cat.of (BasisFrame R I)

noncomputable def coordIndexedCategory (R : Type u) [CommRing R] (I : Type v) :
    ObjCat.{max (u + 1) (v + 1), max u v} :=
  Cat.of (Coord R I)

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

noncomputable def genFrameIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    CategoryRealization Modules.GenFrameIndexedExpr (genFrameIndexedCategory R I) where
  familyFibre := some (.mk genFrameIndexedFamilyRealization {
    parameter := ⟨CommRingCat.of R, I⟩
    parameterQuotation := .commRingIndexTypeRI (CommRingCat.of R) I
    category_eq := by rfl })

noncomputable def basisFrameIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    CategoryRealization Modules.BasisFrameIndexedExpr (basisFrameIndexedCategory R I) where
  familyFibre := some (.mk basisFrameIndexedFamilyRealization {
    parameter := ⟨CommRingCat.of R, I⟩
    parameterQuotation := .commRingIndexTypeRI (CommRingCat.of R) I
    category_eq := by rfl })

noncomputable def coordIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    CategoryRealization Modules.CoordIndexedExpr (coordIndexedCategory R I) where
  familyFibre := some (.mk coordIndexedFamilyRealization {
    parameter := ⟨CommRingCat.of R, I⟩
    parameterQuotation := .commRingIndexTypeRI (CommRingCat.of R) I
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
      (basisFrameToGenFrame R (Fin n)) :=
  { sourceRealization := basisFrameRealization R n
    targetRealization := genFrameRealization R n }

noncomputable def fromBasisFrameRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization Modules.FromBasisFrameExpr
      (basisFrameCategory R n) (coordCategory R n)
      (Coord.fromBasisFrame R (Fin n)) :=
  { sourceRealization := basisFrameRealization R n
    targetRealization := coordRealization R n }

noncomputable def coordForgetRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization Modules.CoordForgetExpr
      (coordCategory R n) (Modules.Mathlib.ModulesOf (RingCat.of R))
      (Coord.forget R (Fin n)) :=
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

noncomputable def genFrameForgetIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    FunctorRealization Modules.GenFrameForgetExpr
      (genFrameIndexedCategory R I)
    (Modules.Mathlib.ModulesOf.{u, max u v} (RingCat.of R))
      (GenFrame.forget R I) :=
  { sourceRealization := genFrameIndexedRealization R I
    targetRealization := modulesRealization.{u, max u v} (RingCat.of R) }

noncomputable def basisFrameForgetIndexedRealization (R : Type u) [CommRing R] (I : Type v) :
    FunctorRealization Modules.BasisFrameForgetExpr
      (basisFrameIndexedCategory R I)
    (Modules.Mathlib.ModulesOf.{u, max u v} (RingCat.of R))
      (BasisFrame.forget R I) :=
  { sourceRealization := basisFrameIndexedRealization R I
    targetRealization := modulesRealization.{u, max u v} (RingCat.of R) }

noncomputable def genFrameForgetIndexedDeclaration (R : Type u) [CommRing R] (I : Type v) :
    genFrameIndexedCategory R I ⥤ Modules.Mathlib.ModulesOf.{u, max u v} (RingCat.of R) :=
  GenFrame.forget R I

noncomputable def basisFrameForgetIndexedDeclaration (R : Type u) [CommRing R] (I : Type v) :
    basisFrameIndexedCategory R I ⥤ Modules.Mathlib.ModulesOf.{u, max u v} (RingCat.of R) :=
  BasisFrame.forget R I

/-! The indexed registrations keep ring and index universes independent. -/
universe uR uI

example (R : Type uR) [CommRing R] (I : Type uI) :
    CategoryRealization Modules.GenFrameIndexedExpr
      (genFrameIndexedCategory R I) :=
  genFrameIndexedRealization R I

example (R : Type uR) [CommRing R] (I : Type uI) :
    CategoryRealization Modules.BasisFrameIndexedExpr
      (basisFrameIndexedCategory R I) :=
  basisFrameIndexedRealization R I

example (R : Type uR) [CommRing R] :
    CategoryRealization Modules.CoordIndexedExpr
      (coordIndexedCategory R (Nat → Nat)) :=
  coordIndexedRealization R (Nat → Nat)

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
  { id := CategoryFamilyId.modules,
    schema := .ring
    realization := `LeanCategories.Modules.CatalogueRegistration.modulesFamilyRealization
    transport := `LeanCategories.Modules.Mathlib.moduleCatRestrictScalarsPseudofunctor
    transportSemantics := .restrictionOfScalars }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.genFrame,
    schema := .commRingNat
    realization := `LeanCategories.Modules.CatalogueRegistration.genFrameFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.genFrameFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.basisFrame,
    schema := .commRingNat
    realization := `LeanCategories.Modules.CatalogueRegistration.basisFrameFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.basisFrameFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.coord,
    schema := .commRingNat
    realization := `LeanCategories.Modules.CatalogueRegistration.coordFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.coordFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.genFrameIndexed,
    schema := .commRingIndexType
    realization := `LeanCategories.Modules.CatalogueRegistration.genFrameIndexedFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.genFrameIndexedFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.basisFrameIndexed,
    schema := .commRingIndexType
    realization := `LeanCategories.Modules.CatalogueRegistration.basisFrameIndexedFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.basisFrameIndexedFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.coordIndexed,
    schema := .commRingIndexType
    realization := `LeanCategories.Modules.CatalogueRegistration.coordIndexedFamilyRealization
    transport := `LeanCategories.Modules.CatalogueRegistration.coordIndexedFamilyTransport
    transportSemantics := .discrete }

normalized_registry .classifier
  { id := ClassifierId.modulesFree,
    declaration := `LeanCategories.Modules.Mathlib.free
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.freeRealization}
normalized_registry .classifier
  { id := ClassifierId.modulesFinitelyGenerated,
    declaration := `LeanCategories.Modules.Mathlib.finitelyGenerated
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.finitelyGeneratedRealization}
normalized_registry .classifier
  { id := ClassifierId.modulesFiniteRank,
    declaration := `LeanCategories.Modules.Mathlib.finiteRank
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.finiteRankRealization}

normalized_registry .category
  { id := CategoryId.modulesR,
    declaration := `LeanCategories.Modules.Mathlib.ModulesOf
    expression := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.modulesRealization}
normalized_registry .category
  { id := CategoryId.freeModules,
    declaration := `LeanCategories.Modules.Mathlib.FreeModules
    expression := Modules.FreeModules
    realization := `LeanCategories.Modules.CatalogueRegistration.freeModulesRealization}
normalized_registry .category
  { id := CategoryId.finitelyGeneratedModules
    declaration := `LeanCategories.Modules.Mathlib.FinitelyGeneratedModules
    expression := Modules.FinitelyGeneratedModules
    realization := `LeanCategories.Modules.CatalogueRegistration.finitelyGeneratedModulesRealization}
normalized_registry .category
  { id := CategoryId.finiteRankModules,
    declaration := `LeanCategories.Modules.Mathlib.FiniteRankModules
    expression := Modules.FiniteRankModules
    realization := `LeanCategories.Modules.CatalogueRegistration.finiteRankModulesRealization}

normalized_registry .category
  { id := CategoryId.genFrame,
    declaration := `LeanCategories.Modules.CatalogueRegistration.genFrameCategory
    expression := Modules.GenFrameExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.genFrameRealization }
normalized_registry .category
  { id := CategoryId.basisFrame,
    declaration := `LeanCategories.Modules.CatalogueRegistration.basisFrameCategory
    expression := Modules.BasisFrameExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.basisFrameRealization }
normalized_registry .category
  { id := CategoryId.coord,
    declaration := `LeanCategories.Modules.CatalogueRegistration.coordCategory
    expression := Modules.CoordExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.coordRealization }
normalized_registry .category
  { id := CategoryId.genFrameIndexed,
    declaration := `LeanCategories.Modules.CatalogueRegistration.genFrameIndexedCategory
    expression := Modules.GenFrameIndexedExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.genFrameIndexedRealization }
normalized_registry .category
  { id := CategoryId.basisFrameIndexed,
    declaration := `LeanCategories.Modules.CatalogueRegistration.basisFrameIndexedCategory
    expression := Modules.BasisFrameIndexedExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.basisFrameIndexedRealization }
normalized_registry .category
  { id := CategoryId.coordIndexed,
    declaration := `LeanCategories.Modules.CatalogueRegistration.coordIndexedCategory
    expression := Modules.CoordIndexedExpr
    realization := `LeanCategories.Modules.CatalogueRegistration.coordIndexedRealization }

normalized_registry .functor
  { id := FunctorId.basisFrameToGenFrame,
    source := Modules.BasisFrameExpr
    target := Modules.GenFrameExpr
    declaration := `LeanCategories.Modules.CatalogueRegistration.basisFrameToGenFrameDeclaration
    realization :=
      `LeanCategories.Modules.CatalogueRegistration.basisFrameToGenFrameRealization
    expression := Modules.BasisFrameToGenFrameExpr }
normalized_registry .functor
  { id := FunctorId.fromBasisFrame,
    source := Modules.BasisFrameExpr
    target := Modules.CoordExpr
    declaration := `LeanCategories.Modules.CatalogueRegistration.fromBasisFrameDeclaration
    realization := `LeanCategories.Modules.CatalogueRegistration.fromBasisFrameRealization
    expression := Modules.FromBasisFrameExpr }
normalized_registry .functor
  { id := FunctorId.coordForget,
    source := Modules.CoordExpr
    target := Modules.Modules
    declaration := `LeanCategories.Modules.CatalogueRegistration.coordForgetDeclaration
    realization := `LeanCategories.Modules.CatalogueRegistration.coordForgetRealization
    expression := Modules.CoordForgetExpr }
normalized_registry .functor
  { id := FunctorId.genFrameForget,
    source := Modules.GenFrameIndexedExpr
    target := Modules.Modules
    declaration := `LeanCategories.Modules.CatalogueRegistration.genFrameForgetIndexedDeclaration
    realization :=
      `LeanCategories.Modules.CatalogueRegistration.genFrameForgetIndexedRealization
    expression := Modules.GenFrameForgetExpr }
normalized_registry .functor
  { id := FunctorId.basisFrameForget,
    source := Modules.BasisFrameIndexedExpr
    target := Modules.Modules
    declaration := `LeanCategories.Modules.CatalogueRegistration.basisFrameForgetIndexedDeclaration
    realization :=
      `LeanCategories.Modules.CatalogueRegistration.basisFrameForgetIndexedRealization
    expression := Modules.BasisFrameForgetExpr }

end
end LeanCategories.Modules.CatalogueRegistration
