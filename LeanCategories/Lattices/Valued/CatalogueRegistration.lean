module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.BaseChange
public import LeanCategories.Lattices.Valued.Catalogue
public import LeanCategories.Lattices.Valued.ChangeValue
public import LeanCategories.Lattices.Valued.DefiniteIndefinite
public import LeanCategories.Lattices.Valued.Expressions
public import LeanCategories.Lattices.Valued.ScaleAndEvenness
public import LeanCategories.Modules.Mathlib
public import LeanCategories.Modules.CatalogueRegistration
public import LeanCategories.Modules.Expressions
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Lattices.Valued.Catalogue
public meta import LeanCategories.Lattices.Valued.Expressions
public meta import LeanCategories.Modules.Catalogue

@[expose] public section

namespace LeanCategories.Lattices.Valued.CatalogueRegistration

open CategoryTheory
open LeanCategories
open LeanCategories.Lattices.Valued.Catalogue

universe u

noncomputable def latticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ R : CommRingCat.{u}, ModuleCat.{u} R)
    (fun (parameter : Σ R : CommRingCat.{u}, ModuleCat.{u} R) =>
    letI := parameter.1.commRing
    (Cat.of (LatticeCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def latticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u, u + 1} CategoryFamilyId.lattice .commRingModule where
  transport := latticeFamilyTransport
  transportSemantics := .discrete

noncomputable def finiteProjectiveLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ R : CommRingCat.{u}, ModuleCat.{u} R)
    (fun (parameter : Σ R : CommRingCat.{u}, ModuleCat.{u} R) =>
      letI := parameter.1.commRing
      (Cat.of (FiniteProjectiveLatticeCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def finiteProjectiveLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u, u + 1}
      CategoryFamilyId.finiteProjectiveLattice .commRingModule where
  transport := finiteProjectiveLatticeFamilyTransport
  transportSemantics := .discrete

noncomputable def finiteFreeLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ R : CommRingCat.{u}, ModuleCat.{u} R)
    (fun (parameter : Σ R : CommRingCat.{u}, ModuleCat.{u} R) =>
      letI := parameter.1.commRing
      (Cat.of (FiniteFreeLatticeCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def finiteFreeLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u, u + 1} CategoryFamilyId.finiteFreeLattice .commRingModule where
  transport := finiteFreeLatticeFamilyTransport
  transportSemantics := .discrete

noncomputable def evenLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1} (P := CommRingCat.{u})
    (fun (R : CommRingCat.{u}) =>
    letI := R.commRing
    (Cat.of (EvenLatticeCat (R := R)) : ObjCat.{u + 1, u}))

noncomputable def evenLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u, u + 1} CategoryFamilyId.evenLattice .commRing where
  transport := evenLatticeFamilyTransport
  transportSemantics := .discrete

noncomputable def latticeCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] : ObjCat.{u + 1, u} :=
  Cat.of (LatticeCat R W)

noncomputable def finiteProjectiveLatticeCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] : ObjCat.{u + 1, u} :=
  Cat.of (FiniteProjectiveLatticeCat R W)

noncomputable def finiteFreeLatticeCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] : ObjCat.{u + 1, u} :=
  Cat.of (FiniteFreeLatticeCat R W)

noncomputable def evenLatticeCategory (R : Type u) [CommRing R] : ObjCat.{u + 1, u} :=
  Cat.of (EvenLatticeCat (R := R))

noncomputable def definiteLatticeCategory : ObjCat := Cat.of DefiniteLatticeCat

noncomputable def indefiniteLatticeCategory : ObjCat := Cat.of IndefiniteLatticeCat

noncomputable def latticeRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization Lattice (latticeCategory R W) where
  familyFibre := some (.mk latticeFamilyRealization {
    parameter := ⟨CommRingCat.of R, ModuleCat.of R W⟩
    parameterQuotation := .commRingModuleRW (CommRingCat.of R) (ModuleCat.of R W)
    category_eq := by rfl })

noncomputable def finiteProjectiveLatticeRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization FiniteProjectiveLattice (finiteProjectiveLatticeCategory R W) where
  familyFibre := some (.mk finiteProjectiveLatticeFamilyRealization {
    parameter := ⟨CommRingCat.of R, ModuleCat.of R W⟩
    parameterQuotation := .commRingModuleRW (CommRingCat.of R) (ModuleCat.of R W)
    category_eq := by rfl })

noncomputable def finiteFreeLatticeRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization FiniteFreeLattice (finiteFreeLatticeCategory R W) where
  familyFibre := some (.mk finiteFreeLatticeFamilyRealization {
    parameter := ⟨CommRingCat.of R, ModuleCat.of R W⟩
    parameterQuotation := .commRingModuleRW (CommRingCat.of R) (ModuleCat.of R W)
    category_eq := by rfl })

noncomputable def evenLatticeRealization (R : Type u) [CommRing R] :
    CategoryRealization EvenLattice (evenLatticeCategory R) where
  familyFibre := some (.mk evenLatticeFamilyRealization {
    parameter := ⟨CommRingCat.of R⟩
    parameterQuotation := .commRingR (CommRingCat.of R)
    category_eq := by rfl })

noncomputable def definiteLatticeRealization :
    CategoryRealization DefiniteLattice definiteLatticeCategory := { familyFibre := none }

noncomputable def indefiniteLatticeRealization :
    CategoryRealization IndefiniteLattice indefiniteLatticeCategory := { familyFibre := none }

noncomputable def latticeChangeValueRealization (R : Type u) [CommRing R]
    (W W' : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W') :
    FunctorRealization LatticeChangeValue (latticeCategory R W)
      (latticeCategory R W')
      (LeanCategories.Lattices.Valued.changeValue R W f).toCatHom :=
  { sourceRealization := latticeRealization R W
    targetRealization :=
       { familyFibre := some (.mk latticeFamilyRealization {
          parameter := ⟨CommRingCat.of R, ModuleCat.of R W'⟩
          parameterQuotation := .commRingModuleRWPrime (CommRingCat.of R) (ModuleCat.of R W')
          category_eq := by rfl }) } }

noncomputable def latticeBaseChangeRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W]
    (S : Type u) [CommRing S] [Algebra R S] :
    FunctorRealization LatticeBaseChange (latticeCategory R W)
      (latticeCategory S (TensorProduct R S W))
      (LeanCategories.Lattices.Valued.baseChange R W S).toCatHom :=
  { sourceRealization := latticeRealization R W
    targetRealization :=
       { familyFibre := some (.mk latticeFamilyRealization {
          parameter := ⟨CommRingCat.of S, ModuleCat.of S (TensorProduct R S W)⟩
          parameterQuotation := .commRingModuleTensorProduct R S W
          category_eq := by rfl }) } }

noncomputable def finiteProjectiveForgetRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    FunctorRealization FiniteProjectiveForget (finiteProjectiveLatticeCategory R W)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Lattices.Valued.finiteProjectiveForget R W).toCatHom :=
  { sourceRealization := finiteProjectiveLatticeRealization R W
    targetRealization := LeanCategories.Modules.CatalogueRegistration.modulesRealization (RingCat.of R) }

noncomputable def latticeChangeValueDeclaration (R : Type u) [CommRing R]
    (W W' : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W') :
    latticeCategory R W ⟶ latticeCategory R W' :=
  (LeanCategories.Lattices.Valued.changeValue R W f).toCatHom

noncomputable def latticeBaseChangeDeclaration (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W]
    (S : Type u) [CommRing S] [Algebra R S] :
    latticeCategory R W ⟶ latticeCategory S (TensorProduct R S W) :=
  (LeanCategories.Lattices.Valued.baseChange R W S).toCatHom

noncomputable def finiteProjectiveForgetDeclaration (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    finiteProjectiveLatticeCategory R W ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (LeanCategories.Lattices.Valued.finiteProjectiveForget R W).toCatHom

normalized_registry .categoryFamily
  { id := CategoryFamilyId.lattice
    canonicalName := "LatticeCat(R, W)"
    schema := .commRingModule
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeFamilyRealization
    transport :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeFamilyTransport
    transportSemantics := .discrete }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.finiteProjectiveLattice
    canonicalName := "FiniteProjectiveLatticeCat(R, W)"
    schema := .commRingModule
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveLatticeFamilyRealization
    transport :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveLatticeFamilyTransport
    transportSemantics := .discrete }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.finiteFreeLattice
    canonicalName := "FiniteFreeLatticeCat(R, W)"
    schema := .commRingModule
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteFreeLatticeFamilyRealization
    transport :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteFreeLatticeFamilyTransport
    transportSemantics := .discrete }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.evenLattice
    canonicalName := "EvenLatticeCat(R)"
    schema := .commRing
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.evenLatticeFamilyRealization
    transport :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.evenLatticeFamilyTransport
    transportSemantics := .discrete }

normalized_registry .category
  { id := CategoryId.lattice
    canonicalName := "LatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeCategory
    expression := Lattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .category
  { id := CategoryId.finiteProjectiveLattice
    canonicalName := "FiniteProjectiveLatticeCat"
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveLatticeCategory
    expression := FiniteProjectiveLattice
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveLatticeRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .category
  { id := CategoryId.finiteFreeLattice
    canonicalName := "FiniteFreeLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteFreeLatticeCategory
    expression := FiniteFreeLattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteFreeLatticeRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .category
  { id := CategoryId.evenLattice
    canonicalName := "EvenLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.evenLatticeCategory
    expression := EvenLattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.evenLatticeRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .category
  { id := CategoryId.definiteLattice
    canonicalName := "DefiniteLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.definiteLatticeCategory
    expression := DefiniteLattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.definiteLatticeRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .category
  { id := CategoryId.indefiniteLattice
    canonicalName := "IndefiniteLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.indefiniteLatticeCategory
    expression := IndefiniteLattice
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.indefiniteLatticeRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .functor
  { id := FunctorId.latticeChangeValue
    canonicalName := "LatticeCat.changeValue"
    source := Lattice
    target :=
      .familyApp CategoryFamilyId.lattice
        #[.variable ParameterId.r, .variable ParameterId.wPrime]
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeChangeValueDeclaration
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeChangeValueRealization
    expression := LatticeChangeValue
    role := .constructorAction
    admissibility := .declared
    port := none
    origin := "existing lattice value change"
    preferredPresentation := false }

normalized_registry .functor
  { id := FunctorId.latticeBaseChange
    canonicalName := "LatticeCat.baseChange"
    source := Lattice
    target :=
      .familyApp CategoryFamilyId.lattice
        #[.variable ParameterId.s,
          .apply3 ParameterOperationId.tensorProduct
            (.variable ParameterId.r) (.variable ParameterId.s) (.variable ParameterId.w)]
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeBaseChangeDeclaration
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeBaseChangeRealization
    expression := LatticeBaseChange
    role := .constructorAction
    admissibility := .declared
    port := none
    origin := "existing lattice scalar extension"
    preferredPresentation := false }

normalized_registry .functor
  { id := FunctorId.finiteProjectiveForget
    canonicalName := "FiniteProjectiveLatticeCat.forget"
    source := FiniteProjectiveLattice
    target := Modules.Modules
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveForgetDeclaration
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveForgetRealization
    expression := FiniteProjectiveForget
    role := .generatedStructural
    admissibility := .generated
    port := none
    origin := "existing finite-projective lattice forgetful functor"
    preferredPresentation := false }

end LeanCategories.Lattices.Valued.CatalogueRegistration
