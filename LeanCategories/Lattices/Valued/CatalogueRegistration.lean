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
    CategoryRealization Lattice (latticeCategory R W) := ⟨⟩

noncomputable def finiteProjectiveLatticeRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization FiniteProjectiveLattice (finiteProjectiveLatticeCategory R W) := ⟨⟩

noncomputable def finiteFreeLatticeRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization FiniteFreeLattice (finiteFreeLatticeCategory R W) := ⟨⟩

noncomputable def evenLatticeRealization (R : Type u) [CommRing R] :
    CategoryRealization EvenLattice (evenLatticeCategory R) := ⟨⟩

noncomputable def definiteLatticeRealization :
    CategoryRealization DefiniteLattice definiteLatticeCategory := ⟨⟩

noncomputable def indefiniteLatticeRealization :
    CategoryRealization IndefiniteLattice indefiniteLatticeCategory := ⟨⟩

noncomputable def latticeChangeValueRealization (R : Type u) [CommRing R]
    (W W' : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W') :
    FunctorRealization LatticeChangeValue (latticeCategory R W)
      (latticeCategory R W')
      (LeanCategories.Lattices.Valued.changeValue R W f).toCatHom := ⟨⟩

noncomputable def latticeBaseChangeRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W]
    (S : Type u) [CommRing S] [Algebra R S] :
    FunctorRealization LatticeBaseChange (latticeCategory R W)
      (latticeCategory S (TensorProduct R S W))
      (LeanCategories.Lattices.Valued.baseChange R W S).toCatHom := ⟨⟩

noncomputable def finiteProjectiveForgetRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    FunctorRealization FiniteProjectiveForget (finiteProjectiveLatticeCategory R W)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Lattices.Valued.finiteProjectiveForget R W).toCatHom := ⟨⟩

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
    coherenceClass := none
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
    coherenceClass := none
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
    coherenceClass := none
    preferredPresentation := false }

end LeanCategories.Lattices.Valued.CatalogueRegistration
