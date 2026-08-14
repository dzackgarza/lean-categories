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

/- These named categories remain atoms until their pullback realizations exist. -/
def Semigroups : CategoryExpr := .atom CategoryId.semigroups
def Monoids : CategoryExpr := .atom CategoryId.monoids
def Groups : CategoryExpr := .atom CategoryId.groups

def AdditiveMagmas : CategoryExpr :=
  .atom CategoryId.additiveMagmas

def AdditiveSemigroups : CategoryExpr :=
  .atom CategoryId.additiveSemigroups

def AdditiveMonoids : CategoryExpr :=
  .atom CategoryId.additiveMonoids

def AdditiveGroups : CategoryExpr :=
  .atom CategoryId.additiveGroups

end LeanCategories.Algebra.Catalogue.Magmas
