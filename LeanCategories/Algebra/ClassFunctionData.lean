/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.RepresentationTheory.Character

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

/-- Proof-free carrier for class functions on a group: functions on the
conjugacy-class quotient (FC01-C18-U025). -/
abbrev ClassFunctionData (G : Type v) [Group G] (F : Type u) : Type (max u v) :=
  ConjClasses G → F

def ClassFunctionData.eval {G : Type v} [Group G] {F : Type u}
    (φ : ClassFunctionData G F) (g : G) : F :=
  φ (ConjClasses.mk g)

/-- The raw character function afforded by a finite-dimensional representation. -/
noncomputable abbrev representationCharacterData
    {k : Type u} [Field k] {G : Type v} [Group G] (V : FDRep k G) : G → k :=
  V.character

/-- The degree data of a character afforded by a representation. -/
noncomputable abbrev representationCharacterDegree
    {k : Type u} [Field k] {G : Type v} [Group G] (V : FDRep k G) : ℕ :=
  Module.finrank k V

abbrev CharacterTableData (ι : Type*) (G : Type v) [Group G] (F : Type u) :=
  ι → ConjClasses G → F

def characterTableOfClassFunctions {ι : Type*} {G : Type v} [Group G] {F : Type u}
    (χ : ι → ClassFunctionData G F) : CharacterTableData ι G F :=
  χ

end LeanCategories.Algebra
