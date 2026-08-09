/-
Data specimens (`expr*`) for the F₂ viability integration test, extracted into
their own module so `Viability.lean` can import them both `public` (for theorem
statements) and `public meta` (so `native_decide` can compile them).
-/
module

public import LeanCategories.CategoryGraph.Core.Expr
public import LeanCategories.CategoryGraph.Core.Ids
public import LeanCategories.CategoryGraph.Categories.Algebra.Magmas
public import LeanCategories.CategoryGraph.Categories.Algebra.Rings
public import LeanCategories.CategoryGraph.Core.StructuralMap
public import LeanCategories.CategoryGraph.Realization.Mathlib.Atomic

@[expose] public section

namespace CategoryGraph.Specimen

open CategoryGraph

def exprSets : CategoryExpr := .atom CategoryId.sets

def exprSetsIdentity : FunctorExpr exprSets exprSets := .identity exprSets

def exprSetsIdentityPullback : CategoryExpr :=
  .pullback (FunctorId.mk "fun.sets.identity") (FunctorId.mk "fun.sets.identity") exprSets

def exprRegisteredSetsIdentity : FunctorExpr exprSets exprSets :=
  .named (FunctorId.mk "fun.sets.identity")

def exprMagmas : CategoryExpr := Categories.Algebra.Magmas.Magmas

def exprSemigroups : CategoryExpr := Categories.Algebra.Magmas.Semigroups

def exprMonoids : CategoryExpr := Categories.Algebra.Magmas.Monoids

def exprGroups : CategoryExpr := Categories.Algebra.Magmas.Groups

def exprAdditiveMagmas : CategoryExpr :=
  .refine exprMagmas ClassifierId.magmasAdditive none

def exprAdditiveSemigroups : CategoryExpr :=
  .refine exprAdditiveMagmas ClassifierId.magmasAssociative (some RouteId.additive)

def exprAdditiveMonoids : CategoryExpr :=
  .refine exprAdditiveSemigroups ClassifierId.magmasUnital (some RouteId.additive)

def exprAdditiveGroups : CategoryExpr :=
  .refine exprAdditiveMonoids ClassifierId.magmasInverse (some RouteId.additive)

def exprMagmasWithTwoOperations : CategoryExpr :=
  Categories.Algebra.Rings.MagmasWithTwoOperations

def exprRings : CategoryExpr := Categories.Algebra.Rings.Rings

def exprCommRings : CategoryExpr := Categories.Algebra.Rings.CommutativeRings

def exprDivisionRings : CategoryExpr :=
  .refine (.atom CategoryId.rings) ClassifierId.ringsDivision none

def exprModules : CategoryExpr :=
  .familyApp CategoryFamilyId.modules #[.ringVariable RingParameterId.r]

def exprRightModules : CategoryExpr :=
  .familyApp CategoryFamilyId.modules #[.opposite (.ringVariable RingParameterId.r)]

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

end CategoryGraph.Specimen
