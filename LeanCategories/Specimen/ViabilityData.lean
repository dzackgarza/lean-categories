/-
Data specimens (`expr*`) for the F₂ viability integration test, extracted into
their own module so `Viability.lean` can import them both `public` (for theorem
statements) and `public meta` (so `native_decide` can compile them).
-/
module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Catalogue.Id
public import LeanCategories.Algebra.Magmas
public import LeanCategories.Algebra.Rings
public import LeanCategories.Catalogue.StructuralMap
public import LeanCategories.Realization.Mathlib.Atomic

@[expose] public section

namespace LeanCategories.Specimen

open LeanCategories

def exprSets : CategoryExpr := .atom CategoryId.sets

def exprSetsIdentity : FunctorExpr exprSets exprSets := .identity exprSets

def exprSetsIdentityPullback : CategoryExpr :=
  .pullback (FunctorId.mk "fun.sets.identity") (FunctorId.mk "fun.sets.identity") exprSets

def exprRegisteredSetsIdentity : FunctorExpr exprSets exprSets :=
  .named (FunctorId.mk "fun.sets.identity")

def exprMagmas : CategoryExpr := Algebra.Magmas.Magmas

def exprSemigroups : CategoryExpr := Algebra.Magmas.Semigroups

def exprMonoids : CategoryExpr := Algebra.Magmas.Monoids

def exprGroups : CategoryExpr := Algebra.Magmas.Groups

def exprAdditiveMagmas : CategoryExpr :=
  .refine exprMagmas ClassifierId.magmasAdditive none

def exprAdditiveSemigroups : CategoryExpr :=
  .refine exprAdditiveMagmas ClassifierId.magmasAssociative (some RouteId.additive)

def exprAdditiveMonoids : CategoryExpr :=
  .refine exprAdditiveSemigroups ClassifierId.magmasUnital (some RouteId.additive)

def exprAdditiveGroups : CategoryExpr :=
  .refine exprAdditiveMonoids ClassifierId.magmasInverse (some RouteId.additive)

def exprMagmasWithTwoOperations : CategoryExpr :=
  Algebra.Rings.MagmasWithTwoOperations

def exprRings : CategoryExpr := Algebra.Rings.Rings

def exprCommRings : CategoryExpr := Algebra.Rings.CommutativeRings

def exprDivisionRings : CategoryExpr :=
  .refine (.atom CategoryId.rings) ClassifierId.ringsDivision none

def exprModules : CategoryExpr :=
  .familyApp CategoryFamilyId.modules #[.variable ParameterId.r]

def exprRightModules : CategoryExpr :=
  .familyApp CategoryFamilyId.modules
    #[.apply ParameterOperationId.opposite (.variable ParameterId.r)]

def exprFreeModules : CategoryExpr :=
  .refine exprModules ClassifierId.modulesFree none

def exprFinitelyGeneratedModules : CategoryExpr :=
  .refine exprModules ClassifierId.modulesFinitelyGenerated none

def exprFiniteRankModules : CategoryExpr :=
  .refine exprModules ClassifierId.modulesFiniteRank none

def exprModulesFamily : CategoryExpr :=
  exprModules

def exprRingsGradedFinite : CategoryExpr :=
  .refine
    (.refine (.atom CategoryId.rings) ClassifierId.setsGraded none)
    ClassifierId.setsFinite none

end LeanCategories.Specimen
