module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.BaseChange
public import LeanCategories.Lattices.Valued.Catalogue
public import LeanCategories.Lattices.Valued.ChangeValue
public import LeanCategories.Lattices.Valued.DefiniteIndefinite
public import LeanCategories.Lattices.Valued.Expressions
public import LeanCategories.Lattices.Valued.Framed
public import LeanCategories.Lattices.Valued.MetricDual
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
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1} CategoryFamilyId.lattice .commRingModule
      (P := Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R)) where
  transport := latticeFamilyTransport
  transportSemantics := .discrete
noncomputable def finiteProjectiveLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ R : CommRingCat.{u}, ModuleCat.{u} R)
    (fun (parameter : Σ R : CommRingCat.{u}, ModuleCat.{u} R) =>
      letI := parameter.1.commRing
      (Cat.of (FiniteProjectiveLatticeCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def finiteProjectiveLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.finiteProjectiveLattice .commRingModule
      (P := Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R)) where
  transport := finiteProjectiveLatticeFamilyTransport
  transportSemantics := .discrete
noncomputable def finiteFreeLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ R : CommRingCat.{u}, ModuleCat.{u} R)
    (fun (parameter : Σ R : CommRingCat.{u}, ModuleCat.{u} R) =>
      letI := parameter.1.commRing
      (Cat.of (FiniteFreeLatticeCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def finiteFreeLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1} CategoryFamilyId.finiteFreeLattice .commRingModule
      (P := Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R)) where
  transport := finiteFreeLatticeFamilyTransport
  transportSemantics := .discrete
noncomputable def evenLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1} (P := CommRingCat.{u})
    (fun (R : CommRingCat.{u}) =>
    letI := R.commRing
    (Cat.of (EvenLatticeCat (R := R)) : ObjCat.{u + 1, u}))

noncomputable def evenLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1} CategoryFamilyId.evenLattice .commRing
      (P := Discrete (CommRingCat.{u})) where
  transport := evenLatticeFamilyTransport
  transportSemantics := .discrete

noncomputable def integralLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1} (P := CommRingCat.{u})
    (fun (R : CommRingCat.{u}) =>
      letI := R.commRing
      (Cat.of (IntegralLatticeCat R) : ObjCat.{u + 1, u}))

noncomputable def integralLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.integralLattice .commRing (P := Discrete (CommRingCat.{u})) where
  transport := integralLatticeFamilyTransport
  transportSemantics := .discrete

noncomputable def coordLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ _R : CommRingCat.{u}, Nat)
    (fun (parameter : Σ _R : CommRingCat.{u}, Nat) =>
      letI := parameter.1.commRing
      (Cat.of (CoordLatticeCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def coordLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.coordLattice .commRingNat
      (P := Discrete (Σ _R : CommRingCat.{u}, Nat)) where
  transport := coordLatticeFamilyTransport
  transportSemantics := .discrete

noncomputable def fractionFieldPerfectFiniteProjectiveLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := PSigma fun R : CommRingCat.{u} => IsDomain R)
    (fun (parameter : PSigma fun R : CommRingCat.{u} => IsDomain R) =>
      letI := parameter.1.commRing
      letI := parameter.2
      (Cat.of (FractionFieldPerfectFiniteProjectiveLatticeCat parameter.1) :
        ObjCat.{u + 1, u}))

noncomputable def fractionFieldPerfectFiniteProjectiveLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.fractionFieldPerfectFiniteProjectiveLattice .domain
      (P := Discrete (PSigma fun R : CommRingCat.{u} => IsDomain R)) where
  transport := fractionFieldPerfectFiniteProjectiveLatticeFamilyTransport
  transportSemantics := .discrete

noncomputable def unimodularLatticeFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := PSigma fun R : CommRingCat.{u} => IsDomain R)
    (fun (parameter : PSigma fun R : CommRingCat.{u} => IsDomain R) =>
      letI := parameter.1.commRing
      letI := parameter.2
      (Cat.of (UnimodularLatticeCat parameter.1) : ObjCat.{u + 1, u}))

noncomputable def unimodularLatticeFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.unimodularLattice .domain
      (P := Discrete (PSigma fun R : CommRingCat.{u} => IsDomain R)) where
  transport := unimodularLatticeFamilyTransport
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

noncomputable def integralLatticeCategory (R : Type u) [CommRing R] : ObjCat.{u + 1, u} :=
  Cat.of (IntegralLatticeCat R)

noncomputable def coordLatticeCategory (R : Type u) [CommRing R] (n : Nat) :
    ObjCat.{u + 1, u} :=
  Cat.of (CoordLatticeCat R n)

noncomputable def fractionFieldPerfectFiniteProjectiveLatticeCategory
    (R : Type u) [CommRing R] [IsDomain R] : ObjCat.{u + 1, u} :=
  Cat.of (FractionFieldPerfectFiniteProjectiveLatticeCat R)

noncomputable def unimodularLatticeCategory
    (R : Type u) [CommRing R] [IsDomain R] : ObjCat.{u + 1, u} :=
  Cat.of (UnimodularLatticeCat R)

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

noncomputable def integralLatticeRealization (R : Type u) [CommRing R] :
    CategoryRealization IntegralLattice (integralLatticeCategory R) where
  familyFibre := some (.mk integralLatticeFamilyRealization {
    parameter := ⟨CommRingCat.of R⟩
    parameterQuotation := .commRingR (CommRingCat.of R)
    category_eq := by rfl })

noncomputable def coordLatticeRealization (R : Type u) [CommRing R] (n : Nat) :
    CategoryRealization CoordLattice (coordLatticeCategory R n) where
  familyFibre := some (.mk coordLatticeFamilyRealization {
    parameter := ⟨CommRingCat.of R, n⟩
    parameterQuotation := .commRingNat (CommRingCat.of R) n
    category_eq := by rfl })

noncomputable def fractionFieldPerfectFiniteProjectiveLatticeRealization
    (R : Type u) [CommRing R] [IsDomain R] :
    CategoryRealization FractionFieldPerfectFiniteProjectiveLattice
      (fractionFieldPerfectFiniteProjectiveLatticeCategory R) where
  familyFibre := some (.mk fractionFieldPerfectFiniteProjectiveLatticeFamilyRealization {
    parameter := ⟨CommRingCat.of R, inferInstance⟩
    parameterQuotation := .domain (CommRingCat.of R) inferInstance
    category_eq := by rfl })

noncomputable def unimodularLatticeRealization
    (R : Type u) [CommRing R] [IsDomain R] :
    CategoryRealization UnimodularLattice (unimodularLatticeCategory R) where
  familyFibre := some (.mk unimodularLatticeFamilyRealization {
    parameter := ⟨CommRingCat.of R, inferInstance⟩
    parameterQuotation := .domain (CommRingCat.of R) inferInstance
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
      (LeanCategories.Lattices.Valued.changeValue R W f) :=
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
      (LeanCategories.Lattices.Valued.baseChange R W S) :=
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
    (LeanCategories.Lattices.Valued.finiteProjectiveForget R W) :=
  { sourceRealization := finiteProjectiveLatticeRealization R W
    targetRealization := LeanCategories.Modules.CatalogueRegistration.modulesRealization (RingCat.of R) }

noncomputable def integralLatticeForgetRealization (R : Type u) [CommRing R] :
    FunctorRealization IntegralLatticeForget (integralLatticeCategory R)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (integralLatticeForget R) :=
  { sourceRealization := integralLatticeRealization R
    targetRealization := LeanCategories.Modules.CatalogueRegistration.modulesRealization
      (RingCat.of R) }

noncomputable def coordLatticeToCoordRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization CoordLatticeToCoord (coordLatticeCategory R n)
      (LeanCategories.Modules.CatalogueRegistration.coordCategory R n)
      (coordLatticeToCoord R n) :=
  { sourceRealization := coordLatticeRealization R n
    targetRealization := LeanCategories.Modules.CatalogueRegistration.coordRealization R n }

noncomputable def coordLatticeToIntegralRealization (R : Type u) [CommRing R] (n : Nat) :
    FunctorRealization CoordLatticeToIntegral (coordLatticeCategory R n)
      (integralLatticeCategory R)
      (coordLatticeToIntegral R n) :=
  { sourceRealization := coordLatticeRealization R n
    targetRealization := integralLatticeRealization R }

noncomputable def fractionFieldPerfectFiniteProjectiveForgetRealization
    (R : Type u) [CommRing R] [IsDomain R] :
    FunctorRealization FractionFieldPerfectFiniteProjectiveForget
      (fractionFieldPerfectFiniteProjectiveLatticeCategory R)
      (integralLatticeCategory R)
      (fractionFieldPerfectFiniteProjectiveForget R) :=
  { sourceRealization := fractionFieldPerfectFiniteProjectiveLatticeRealization R
    targetRealization := integralLatticeRealization R }

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

noncomputable def integralLatticeForgetDeclaration (R : Type u) [CommRing R] :
    integralLatticeCategory R ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (integralLatticeForget R).toCatHom

noncomputable def coordLatticeToCoordDeclaration (R : Type u) [CommRing R] (n : Nat) :
    coordLatticeCategory R n ⟶ LeanCategories.Modules.CatalogueRegistration.coordCategory R n :=
  (coordLatticeToCoord R n).toCatHom

noncomputable def coordLatticeToIntegralDeclaration (R : Type u) [CommRing R] (n : Nat) :
    coordLatticeCategory R n ⟶ integralLatticeCategory R :=
  (coordLatticeToIntegral R n).toCatHom

noncomputable def fractionFieldPerfectFiniteProjectiveForgetDeclaration
    (R : Type u) [CommRing R] [IsDomain R] :
    fractionFieldPerfectFiniteProjectiveLatticeCategory R ⟶ integralLatticeCategory R :=
  (fractionFieldPerfectFiniteProjectiveForget R).toCatHom

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
normalized_registry .categoryFamily
  { id := CategoryFamilyId.integralLattice, canonicalName := "IntegralLatticeCat(R)"
    schema := .commRing
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.integralLatticeFamilyRealization
    transport :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.integralLatticeFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.coordLattice, canonicalName := "CoordLatticeCat(R, n)"
    schema := .commRingNat
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.coordLatticeFamilyRealization
    transport :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.coordLatticeFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.fractionFieldPerfectFiniteProjectiveLattice
    canonicalName := "FractionFieldPerfectFiniteProjectiveLatticeCat(R)"
    schema := .domain
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.fractionFieldPerfectFiniteProjectiveLatticeFamilyRealization
    transport :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.fractionFieldPerfectFiniteProjectiveLatticeFamilyTransport
    transportSemantics := .discrete }
normalized_registry .categoryFamily
  { id := CategoryFamilyId.unimodularLattice, canonicalName := "UnimodularLatticeCat(R)"
    schema := .domain
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.unimodularLatticeFamilyRealization
    transport :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.unimodularLatticeFamilyTransport
    transportSemantics := .discrete }

normalized_registry .category
  { id := CategoryId.lattice
    canonicalName := "LatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeCategory
    expression := Lattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.latticeRealization}

normalized_registry .category
  { id := CategoryId.finiteProjectiveLattice
    canonicalName := "FiniteProjectiveLatticeCat"
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveLatticeCategory
    expression := FiniteProjectiveLattice
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveLatticeRealization}

normalized_registry .category
  { id := CategoryId.finiteFreeLattice
    canonicalName := "FiniteFreeLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteFreeLatticeCategory
    expression := FiniteFreeLattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteFreeLatticeRealization}

normalized_registry .category
  { id := CategoryId.evenLattice
    canonicalName := "EvenLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.evenLatticeCategory
    expression := EvenLattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.evenLatticeRealization}

normalized_registry .category
  { id := CategoryId.definiteLattice
    canonicalName := "DefiniteLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.definiteLatticeCategory
    expression := DefiniteLattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.definiteLatticeRealization}

normalized_registry .category
  { id := CategoryId.indefiniteLattice
    canonicalName := "IndefiniteLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.indefiniteLatticeCategory
    expression := IndefiniteLattice
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.indefiniteLatticeRealization}
normalized_registry .category
  { id := CategoryId.integralLattice, canonicalName := "IntegralLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.integralLatticeCategory
    expression := IntegralLattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.integralLatticeRealization }
normalized_registry .category
  { id := CategoryId.coordLattice, canonicalName := "CoordLatticeCat"
    declaration := `LeanCategories.Lattices.Valued.CatalogueRegistration.coordLatticeCategory
    expression := CoordLattice
    realization := `LeanCategories.Lattices.Valued.CatalogueRegistration.coordLatticeRealization }
normalized_registry .category
  { id := CategoryId.fractionFieldPerfectFiniteProjectiveLattice
    canonicalName := "FractionFieldPerfectFiniteProjectiveLatticeCat"
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.fractionFieldPerfectFiniteProjectiveLatticeCategory
    expression := FractionFieldPerfectFiniteProjectiveLattice
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.fractionFieldPerfectFiniteProjectiveLatticeRealization }
normalized_registry .category
  { id := CategoryId.unimodularLattice, canonicalName := "UnimodularLatticeCat"
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.unimodularLatticeCategory
    expression := UnimodularLattice
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.unimodularLatticeRealization }

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
    expression := LatticeChangeValue }

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
    expression := LatticeBaseChange }

normalized_registry .functor
  { id := FunctorId.finiteProjectiveForget
    canonicalName := "FiniteProjectiveLatticeCat.forget"
    source := FiniteProjectiveLattice
    target := Modules.Modules
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveForgetDeclaration
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.finiteProjectiveForgetRealization
    expression := FiniteProjectiveForget }
normalized_registry .functor
  { id := FunctorId.integralLatticeForget, canonicalName := "IntegralLatticeCat.forget"
    source := IntegralLattice
    target := Modules.Modules
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.integralLatticeForgetDeclaration
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.integralLatticeForgetRealization
    expression := IntegralLatticeForget }
normalized_registry .functor
  { id := FunctorId.coordLatticeToCoord, canonicalName := "CoordLatticeCat.toCoord"
    source := CoordLattice
    target := Modules.CoordExpr
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.coordLatticeToCoordDeclaration
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.coordLatticeToCoordRealization
    expression := CoordLatticeToCoord }
normalized_registry .functor
  { id := FunctorId.coordLatticeToIntegral, canonicalName := "CoordLatticeCat.toIntegral"
    source := CoordLattice
    target := IntegralLattice
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.coordLatticeToIntegralDeclaration
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.coordLatticeToIntegralRealization
    expression := CoordLatticeToIntegral }
normalized_registry .functor
  { id := FunctorId.fractionFieldPerfectFiniteProjectiveForget
    canonicalName := "FractionFieldPerfectFiniteProjectiveLatticeCat.forget"
    source := FractionFieldPerfectFiniteProjectiveLattice
    target := IntegralLattice
    declaration :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.fractionFieldPerfectFiniteProjectiveForgetDeclaration
    realization :=
      `LeanCategories.Lattices.Valued.CatalogueRegistration.fractionFieldPerfectFiniteProjectiveForgetRealization
    expression := FractionFieldPerfectFiniteProjectiveForget }

end LeanCategories.Lattices.Valued.CatalogueRegistration
