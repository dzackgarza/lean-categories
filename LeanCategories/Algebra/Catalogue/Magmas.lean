/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Foundation.Catalogue
public import LeanCategories.Algebra.Catalogue

@[expose] public section

/-!
# Magmas cluster — least-host ownership

Owns Magmas and the magma classifiers Associative / Commutative / Unital / Inverse,
plus standard names Semigroups / Monoids / Groups as expressions.
-/

namespace LeanCategories.Algebra.Catalogue.Magmas

open LeanCategories
/-- Magmas := total(BinaryOperation on Sets). -/
def Magmas : CategoryExpr := .classifierTotal ClassifierId.setsBinaryOperation

def Associative : ClassifierId := ClassifierId.magmasAssociative
def Commutative : ClassifierId := ClassifierId.magmasCommutative
def Unital : ClassifierId := ClassifierId.magmasUnital
def Inverse : ClassifierId := ClassifierId.magmasInverse

def Semigroups : CategoryExpr := .refine Magmas Associative none
def Monoids : CategoryExpr := .refine Semigroups Unital none
def Groups : CategoryExpr := .refine Monoids Inverse none

def AdditiveMagmas : CategoryExpr :=
  .refine Magmas ClassifierId.magmasAdditive none

def AdditiveSemigroups : CategoryExpr :=
  .refine AdditiveMagmas Associative (some RouteId.additive)

def AdditiveMonoids : CategoryExpr :=
  .refine AdditiveSemigroups Unital (some RouteId.additive)

def AdditiveGroups : CategoryExpr :=
  .refine AdditiveMonoids Inverse (some RouteId.additive)

end LeanCategories.Algebra.Catalogue.Magmas
