/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Specimen.Viability
public import LeanCategories.Registry.Extension

@[expose] public section

/-!
# Register the viability specimen into the Lean environment

Each command is the authored registry declaration.  There is no parallel snapshot to
replay: importing this module elaborates, validates, and inserts each declaration into
`registryExt` once.
-/

open LeanCategories
open LeanCategories.Specimen

normalized_registry .category
  { id := CategoryId.sets, canonicalName := "Sets"
    declaration := `LeanCategories.Normalized.Sets
    expression := exprSets
    realization := `LeanCategories.Specimen.specimenSetsRealization
    origin := .root, visibility := .present }

normalized_registry .category
  { id := CategoryId.magmas, canonicalName := "Magmas"
    declaration := `LeanCategories.Normalized.Magmas
    expression := exprMagmas
    realization := `LeanCategories.Specimen.specimenMagmasRealization
    origin := .atomicClassifierTotal, visibility := .present }

normalized_registry .category
  { id := CategoryId.unitalMagmas, canonicalName := "UnitalMagmas"
    declaration := `LeanCategories.Realization.Mathlib.UnitalMagmas
    expression := .classifierTotal ClassifierId.magmasUnital
    realization := `LeanCategories.Specimen.specimenUnitalMagmasRealization
    origin := .atomicClassifierTotal, visibility := .semanticOnly }

normalized_registry .category
  { id := CategoryId.semigroups, canonicalName := "Semigroups"
    declaration := `LeanCategories.Normalized.Semigroups
    expression := exprSemigroups
    realization := `LeanCategories.Specimen.specimenSemigroupsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.monoids, canonicalName := "Monoids"
    declaration := `LeanCategories.Normalized.Monoids
    expression := exprMonoids
    realization := `LeanCategories.Specimen.specimenMonoidsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.groups, canonicalName := "Groups"
    declaration := `LeanCategories.Normalized.Groups
    expression := exprGroups
    realization := `LeanCategories.Specimen.specimenGroupsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.additiveMagmas, canonicalName := "AdditiveMagmas"
    declaration := `LeanCategories.Normalized.AdditiveMagmas
    expression := exprAdditiveMagmas
    realization := `LeanCategories.Specimen.specimenAdditiveMagmasRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.additiveSemigroups, canonicalName := "AdditiveSemigroups"
    declaration := `LeanCategories.Normalized.AdditiveSemigroups
    expression := exprAdditiveSemigroups
    realization := `LeanCategories.Specimen.specimenAdditiveSemigroupsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.additiveMonoids, canonicalName := "AdditiveMonoids"
    declaration := `LeanCategories.Normalized.AdditiveMonoids
    expression := exprAdditiveMonoids
    realization := `LeanCategories.Specimen.specimenAdditiveMonoidsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.additiveGroups, canonicalName := "AdditiveGroups"
    declaration := `LeanCategories.Normalized.AdditiveGroups
    expression := exprAdditiveGroups
    realization := `LeanCategories.Specimen.specimenAdditiveGroupsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.rings, canonicalName := "Rings"
    declaration := `LeanCategories.Normalized.Rings
    expression := exprRings
    realization := `LeanCategories.Specimen.specimenRingsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.commutativeRings, canonicalName := "CommutativeRings"
    declaration := `LeanCategories.Normalized.CommutativeRings
    expression := exprCommRings
    realization := `LeanCategories.Specimen.specimenCommRingsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.divisionRings, canonicalName := "DivisionRings"
    declaration := `LeanCategories.Normalized.DivisionRings
    expression := exprDivisionRings
    realization := `LeanCategories.Specimen.specimenDivisionRingsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.modulesR, canonicalName := "Modules(R)"
    declaration := `LeanCategories.Normalized.Modules
    expression := exprModules
    realization := `LeanCategories.Specimen.specimenModulesRealization
    origin := .root, visibility := .present }

normalized_registry .category
  { id := CategoryId.finitelyGeneratedModules, canonicalName := "FinitelyGeneratedModules(R)"
    declaration := `LeanCategories.Normalized.FinitelyGeneratedModules
    expression := exprFinitelyGeneratedModules
    realization := `LeanCategories.Specimen.specimenFinitelyGeneratedModulesRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.finiteRankModules, canonicalName := "FiniteRankModules(R)"
    declaration := `LeanCategories.Normalized.FiniteRankModules
    expression := exprFiniteRankModules
    realization := `LeanCategories.Specimen.specimenFiniteRankModulesRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.freeModules, canonicalName := "FreeModules(R)"
    declaration := `LeanCategories.Normalized.FreeModules
    expression := exprFreeModules
    realization := `LeanCategories.Specimen.specimenFreeModulesRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .category
  { id := CategoryId.magmasWithTwoOperations, canonicalName := "MagmasWithTwoOperations"
    declaration := `LeanCategories.Normalized.MagmasWithTwoOperations
    expression := exprMagmasWithTwoOperations
    realization := `LeanCategories.Specimen.specimenMagmasWithTwoOperationsRealization
    origin := .opaqueCategory, visibility := .semanticOnly }

normalized_registry .category
  { id := CategoryId.crystals, canonicalName := "Crystals"
    declaration := `LeanCategories.Realization.Mathlib.Crystals
    expression := .opaque CategoryId.crystals
    realization := `LeanCategories.Specimen.specimenCrystalsRealization
    origin := .opaqueCategory, visibility := .semanticOnly }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.modules
    canonicalName := "Modules(R)"
    declaration := `LeanCategories.Normalized.Modules
    parameter := { name := "R", kind := .ringObject }
    fibreDeclaration := `LeanCategories.Normalized.Modules
    variance := .restrictionOfScalarsContravariant }

normalized_registry .classifier
  { id := ClassifierId.setsFinite, canonicalName := "Finite"
    declaration := `LeanCategories.Realization.Mathlib.finite
    hostId := CategoryId.sets, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.setsGraded, canonicalName := "Graded"
    declaration := `LeanCategories.Realization.Mathlib.graded
    hostId := CategoryId.sets, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.setsBinaryOperation, canonicalName := "BinaryOperation"
    declaration := `LeanCategories.Realization.Mathlib.binaryOperation
    hostId := CategoryId.sets, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasAssociative, canonicalName := "Associative"
    declaration := `LeanCategories.Realization.Mathlib.associative
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasCommutative, canonicalName := "Commutative"
    declaration := `LeanCategories.Realization.Mathlib.commutative
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasUnital, canonicalName := "Unital"
    declaration := `LeanCategories.Realization.Mathlib.unital
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasInverse, canonicalName := "Inverse"
    declaration := `LeanCategories.Realization.Mathlib.inverse
    hostId := CategoryId.unitalMagmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasAdditive, canonicalName := "Additive"
    declaration := `LeanCategories.Realization.Mathlib.additive
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasMultiplicative, canonicalName := "Multiplicative"
    declaration := `LeanCategories.Realization.Mathlib.multiplicative
    hostId := CategoryId.magmas, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.modulesFree, canonicalName := "Free"
    declaration := `LeanCategories.Realization.Mathlib.free
    hostId := CategoryId.modulesR, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.modulesFinitelyGenerated, canonicalName := "FinitelyGenerated"
    declaration := `LeanCategories.Realization.Mathlib.finitelyGenerated
    hostId := CategoryId.modulesR, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.modulesFiniteRank, canonicalName := "FiniteRank"
    declaration := `LeanCategories.Realization.Mathlib.finiteRank
    hostId := CategoryId.modulesR, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.m2oDistributive, canonicalName := "Distributive"
    declaration := `LeanCategories.Realization.Mathlib.distributive
    hostId := CategoryId.magmasWithTwoOperations, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.ringsDivision, canonicalName := "Division"
    declaration := `LeanCategories.Normalized.divisionOnRings
    hostId := CategoryId.rings, visibility := .present }

normalized_registry .functor
  { id := ⟨"fun.sets.identity"⟩
    canonicalName := "id_Sets"
    source := exprSets
    target := exprSets
    declaration := `LeanCategories.Specimen.specimenSetsIdentity
    realization := `LeanCategories.Specimen.specimenSetsIdentityRealization
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
    declaration := `LeanCategories.Specimen.CRings }

normalized_registry .opaque
  { id := CategoryId.magmasWithTwoOperations
    declaration := `LeanCategories.Realization.Mathlib.MagmasWithTwoOperations
    ports := #[
      { id := ⟨"oport.m2o.multiplicative"⟩
        source := CategoryId.magmasWithTwoOperations
        target := CategoryId.magmas
        role := PortId.multiplicative
        declaration := `LeanCategories.Realization.Mathlib.multiplicativePort
        provenance := "authored opaque interface" },
      { id := ⟨"oport.m2o.additive"⟩
        source := CategoryId.magmasWithTwoOperations
        target := CategoryId.magmas
        role := PortId.additive
        declaration := `LeanCategories.Realization.Mathlib.additivePort
        provenance := "authored opaque interface" }
    ]
    reason := "two-operation host; distributivity is a separate classifier"
    visibility := .semanticOnly }

normalized_registry .opaque
  { id := CategoryId.crystals
    declaration := `LeanCategories.Realization.Mathlib.Crystals
    ports := #[
      { id := ⟨"oport.crystals.sets"⟩
        source := CategoryId.crystals
        target := CategoryId.sets
        role := PortId.underlyingSet
        declaration := `LeanCategories.Realization.Mathlib.crystalsToSets
        provenance := "authored opaque interface" }
    ]
    reason := "exceptional combinatorial host"
    visibility := .semanticOnly }

/--
error: registry declaration LeanCategories.Specimen.exprSets must return ObjCat,
but returns CategoryExpr
-/
#guard_msgs in
normalized_registry .category
  { id := ⟨"cat.invalid.ast"⟩
    canonicalName := "InvalidAST"
    declaration := `LeanCategories.Specimen.exprSets
    expression := exprSets
    realization := `LeanCategories.Specimen.specimenSetsRealization
    origin := .root
    visibility := .semanticOnly }
