/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Constructors
public import LeanCategories.Catalogue.FamilyFibration
public import LeanCategories.Catalogue.Holds
public import LeanCategories.Catalogue.Id
public import LeanCategories.Catalogue.Interpretation
public import LeanCategories.Catalogue.Lift
public import LeanCategories.Catalogue.Realization
public import LeanCategories.Catalogue.Registry.Entry
public import LeanCategories.Catalogue.Registry.Semantic
public import LeanCategories.Catalogue.Registry.Typed
public import LeanCategories.Catalogue.Semantics
public import LeanCategories.Catalogue.Semantics.TotalityProbes
public import LeanCategories.Catalogue.Semantics.EvidenceTests
public import LeanCategories.Catalogue.Semantics.DecidableElementTests
public import LeanCategories.Catalogue.Semantics.FiniteSubsetLiteralTests
public import LeanCategories.Catalogue.Semantics.Algebra.Catalogue
public import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas
public import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Rings
public import LeanCategories.Catalogue.Semantics.Algebra.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Algebra.PortComparison
public import LeanCategories.Catalogue.Semantics.Algebra.Ports
public import LeanCategories.Catalogue.Semantics.Algebra.Properties
public import LeanCategories.Catalogue.Semantics.Algebra.Subgroups
public import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import LeanCategories.Catalogue.Semantics.Exceptional.Catalogue
public import LeanCategories.Catalogue.Semantics.Exceptional.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.FibrationCatalogue
public import LeanCategories.Catalogue.Semantics.FibrationRegistration
public import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public import LeanCategories.Catalogue.Semantics.Foundation.Catalogue
public import LeanCategories.Catalogue.Semantics.Foundation.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Foundation.Expressions
public import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
public import LeanCategories.Catalogue.Semantics.Foundation.Lists
public import LeanCategories.Catalogue.Semantics.Foundation.Objects
public import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
public import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import LeanCategories.Catalogue.Semantics.Algebra.Differentials
public import LeanCategories.Catalogue.Semantics.Algebra.Units
public import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
public import LeanCategories.Catalogue.Semantics.Algebra.Calculus
public import LeanCategories.Catalogue.Semantics.Algebra.MvPolynomials
public import LeanCategories.Catalogue.Semantics.Algebra.Algebras
public import LeanCategories.Catalogue.Semantics.Algebra.Schemes
public import LeanCategories.Catalogue.Semantics.Foundation.PairDiagrams
public import LeanCategories.Catalogue.Semantics.Foundation.Subsets
public import LeanCategories.Catalogue.Semantics.LatticeRefinements
public import LeanCategories.Catalogue.Semantics.Lattices.Valued.Catalogue
public import LeanCategories.Catalogue.Semantics.Lattices.Valued.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Lattices.Valued.Expressions
public import LeanCategories.Catalogue.Semantics.Lattices.Valued.Property
public import LeanCategories.Catalogue.Semantics.Limits.Lifts
public import LeanCategories.Catalogue.Semantics.Limits.Registration
public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Catalogue
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Expressions
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Catalogue.Semantics.Modules.Catalogue
public import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Modules.Expressions
public import LeanCategories.Catalogue.Semantics.Modules.Operations
public import LeanCategories.Catalogue.Semantics.Modules.Quadratic.Valued.Catalogue
public import LeanCategories.Catalogue.Semantics.Modules.Quadratic.Valued.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Modules.Quadratic.Valued.Expressions
public import LeanCategories.Catalogue.Semantics.Modules.Rank
public import LeanCategories.Catalogue.Semantics.Modules.TorsionFree
public import LeanCategories.Catalogue.Semantics.QuadFibrationRegistration
public import LeanCategories.Catalogue.Syntax

/-!
# The CAS catalogue: the semantic registry of `lean-cas-dsl`

The symbolic calculus of categories and functors (`Syntax`), the realization witnesses that tie
each expression to its Lean category (`Realization`, `FamilyFibration`, `Interpretation`), the
semantic registry (`Registry.Semantic`: schema, validators, the `normalized_registry` command) and
its rows (`Semantics`). Declarations live in the namespace `CasCatalogue`, the catalogue's name.
`lean-cas-dsl` imports this at a pinned revision and adds only realizations.
-/
