/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryGraph.Specimen.Viability
public import LeanCategories.CategoryGraph.Registry.Extension

@[expose] public section

/-!
# Register the viability specimen into the Lean environment

Each command is the authored registry declaration.  There is no parallel snapshot to
replay: importing this module elaborates, validates, and inserts each declaration into
`registryExt` once.
-/

open CategoryGraph
open CategoryGraph.Specimen

normalized_registry .category
  { id := CategoryId.sets, canonicalName := "Sets"
    declaration := `CategoryGraph.Normalized.Sets
    expression := exprSets
    realization := some `CategoryGraph.Specimen.specimenSetsRealization
    origin := .root, visibility := .present }

normalized_registry .category
  { id := CategoryId.magmas, canonicalName := "Magmas"
    declaration := `CategoryGraph.Normalized.Magmas
    expression := exprMagmas
    realization := some `CategoryGraph.Specimen.specimenMagmasRealization
    origin := .atomicClassifierTotal, visibility := .present }

normalized_registry .category
  { id := CategoryId.unitalMagmas, canonicalName := "UnitalMagmas"
    declaration := `CategoryGraph.Realization.Mathlib.UnitalMagmas
    expression := .classifierTotal ClassifierId.magmasUnital
    origin := .atomicClassifierTotal, visibility := .semanticOnly }

normalized_registry .category
  { id := CategoryId.semigroups, canonicalName := "Semigroups"
    declaration := `CategoryGraph.Normalized.Semigroups
    expression := exprSemigroups
    realization := some `CategoryGraph.Specimen.specimenSemigroupsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.monoids, canonicalName := "Monoids"
    declaration := `CategoryGraph.Normalized.Monoids
    expression := exprMonoids, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.groups, canonicalName := "Groups"
    declaration := `CategoryGraph.Normalized.Groups
    expression := exprGroups, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.additiveMagmas, canonicalName := "AdditiveMagmas"
    declaration := `CategoryGraph.Normalized.AdditiveMagmas
    expression := exprAdditiveMagmas, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.additiveSemigroups, canonicalName := "AdditiveSemigroups"
    declaration := `CategoryGraph.Normalized.AdditiveSemigroups
    expression := exprAdditiveSemigroups, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.additiveMonoids, canonicalName := "AdditiveMonoids"
    declaration := `CategoryGraph.Normalized.AdditiveMonoids
    expression := exprAdditiveMonoids, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.additiveGroups, canonicalName := "AdditiveGroups"
    declaration := `CategoryGraph.Normalized.AdditiveGroups
    expression := exprAdditiveGroups, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.rings, canonicalName := "Rings"
    declaration := `CategoryGraph.Normalized.Rings
    expression := exprRings, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.commutativeRings, canonicalName := "CommutativeRings"
    declaration := `CategoryGraph.Normalized.CommutativeRings
    expression := exprCommRings, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.divisionRings, canonicalName := "DivisionRings"
    declaration := `CategoryGraph.Normalized.DivisionRings
    expression := exprDivisionRings, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.modulesR, canonicalName := "Modules(R)"
    declaration := `CategoryGraph.Normalized.Modules
    expression := exprModules, origin := .root, visibility := .present }

normalized_registry .category
  { id := CategoryId.finitelyGeneratedModules, canonicalName := "FinitelyGeneratedModules(R)"
    declaration := `CategoryGraph.Normalized.FinitelyGeneratedModules
    expression := exprFinitelyGeneratedModules, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.finiteRankModules, canonicalName := "FiniteRankModules(R)"
    declaration := `CategoryGraph.Normalized.FiniteRankModules
    expression := exprFiniteRankModules, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.freeModules, canonicalName := "FreeModules(R)"
    declaration := `CategoryGraph.Normalized.FreeModules
    expression := exprFreeModules, origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.magmasWithTwoOperations, canonicalName := "MagmasWithTwoOperations"
    declaration := `CategoryGraph.Normalized.MagmasWithTwoOperations
    expression := exprMagmasWithTwoOperations
    realization := some `CategoryGraph.Specimen.specimenMagmasWithTwoOperationsRealization
    origin := .opaqueCategory, visibility := .semanticOnly }

normalized_registry .category
  { id := CategoryId.crystals, canonicalName := "Crystals"
    declaration := `CategoryGraph.Realization.Mathlib.Crystals
    expression := .opaque CategoryId.crystals
    origin := .opaqueCategory, visibility := .semanticOnly }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.modules
    canonicalName := "Modules(R)"
    declaration := `CategoryGraph.Normalized.Modules
    parameter := { name := "R", kind := .ringObject }
    fibreDeclaration := `CategoryGraph.Normalized.Modules
    variance := .restrictionOfScalarsContravariant }

normalized_registry .classifier
  { id := ClassifierId.setsFinite, canonicalName := "Finite"
    declaration := `CategoryGraph.Realization.Mathlib.finite
    hostId := CategoryId.sets, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.setsGraded, canonicalName := "Graded"
    declaration := `CategoryGraph.Realization.Mathlib.graded
    hostId := CategoryId.sets, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.setsBinaryOperation, canonicalName := "BinaryOperation"
    declaration := `CategoryGraph.Realization.Mathlib.binaryOperation
    hostId := CategoryId.sets, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasAssociative, canonicalName := "Associative"
    declaration := `CategoryGraph.Realization.Mathlib.associative
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasCommutative, canonicalName := "Commutative"
    declaration := `CategoryGraph.Realization.Mathlib.commutative
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasUnital, canonicalName := "Unital"
    declaration := `CategoryGraph.Realization.Mathlib.unital
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasInverse, canonicalName := "Inverse"
    declaration := `CategoryGraph.Realization.Mathlib.inverse
    hostId := CategoryId.unitalMagmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasAdditive, canonicalName := "Additive"
    declaration := `CategoryGraph.Realization.Mathlib.additive
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasMultiplicative, canonicalName := "Multiplicative"
    declaration := `CategoryGraph.Realization.Mathlib.multiplicative
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.modulesFree, canonicalName := "Free"
    declaration := `CategoryGraph.Realization.Mathlib.free
    hostId := CategoryId.modulesR, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.modulesFinitelyGenerated, canonicalName := "FinitelyGenerated"
    declaration := `CategoryGraph.Realization.Mathlib.finitelyGenerated
    hostId := CategoryId.modulesR, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.modulesFiniteRank, canonicalName := "FiniteRank"
    declaration := `CategoryGraph.Realization.Mathlib.finiteRank
    hostId := CategoryId.modulesR, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.m2oDistributive, canonicalName := "Distributive"
    declaration := `CategoryGraph.Realization.Mathlib.distributive
    hostId := CategoryId.magmasWithTwoOperations, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.ringsDivision, canonicalName := "Division"
    declaration := `CategoryGraph.Normalized.divisionOnRings
    hostId := CategoryId.rings, visibility := .present }

normalized_registry .functor
  { id := ⟨"fun.sets.identity"⟩
    canonicalName := "id_Sets"
    source := exprSets
    target := exprSets
    declaration := `CategoryGraph.Specimen.specimenSetsIdentity
    expression := exprSetsIdentity
    role := .generatedStructural
    admissibility := .generated
    port := none
    origin := "identity"
    coherenceClass := none
    preferredPresentation := false }

normalized_registry .alias
  { id := AliasId.crings, spelling := "CRings"
    aliasOf := CategoryId.commutativeRings
    declaration := `CategoryGraph.Specimen.CRings }

normalized_registry .opaque
  { id := CategoryId.magmasWithTwoOperations
    declaration := `CategoryGraph.Realization.Mathlib.MagmasWithTwoOperations
    ports := #[
      { id := ⟨"oport.m2o.multiplicative"⟩
        source := CategoryId.magmasWithTwoOperations
        target := CategoryId.magmas
        role := PortId.multiplicative
        declaration := `CategoryGraph.Realization.Mathlib.multiplicativePort
        provenance := "authored opaque interface" },
      { id := ⟨"oport.m2o.additive"⟩
        source := CategoryId.magmasWithTwoOperations
        target := CategoryId.magmas
        role := PortId.additive
        declaration := `CategoryGraph.Realization.Mathlib.additivePort
        provenance := "authored opaque interface" }
    ]
    reason := "two-operation host; distributivity is a separate classifier"
    visibility := .semanticOnly }

normalized_registry .opaque
  { id := CategoryId.crystals
    declaration := `CategoryGraph.Realization.Mathlib.Crystals
    ports := #[
      { id := ⟨"oport.crystals.sets"⟩
        source := CategoryId.crystals
        target := CategoryId.sets
        role := PortId.underlyingSet
        declaration := `CategoryGraph.Realization.Mathlib.crystalsToSets
        provenance := "authored opaque interface" }
    ]
    reason := "exceptional combinatorial host"
    visibility := .semanticOnly }

/--
error: registry declaration CategoryGraph.Specimen.exprSets must return ObjCat,
but returns CategoryExpr
-/
#guard_msgs in
normalized_registry .category
  { id := ⟨"cat.invalid.ast"⟩
    canonicalName := "InvalidAST"
    declaration := `CategoryGraph.Specimen.exprSets
    expression := exprSets
    origin := .root
    visibility := .semanticOnly }
