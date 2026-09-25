/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Complex.Basic
public import Mathlib.RepresentationTheory.Character

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

open scoped BigOperators

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

abbrev VirtualCharacterData (ι : Type*) := ι →₀ ℤ

def virtualCharacterClassFunction
    {ι : Type*} {G : Type v} [Group G] {F : Type u} [AddCommGroup F]
    (χ : ι → ClassFunctionData G F) (z : VirtualCharacterData ι) :
    ClassFunctionData G F :=
  fun c => z.sum fun i n => n • χ i c

/-- The averaging formula for induction of a complex class function from a
subgroup, recorded before proving that the result is conjugation-invariant.

This is the definition-level content behind FC01-C19-U030. The reference
implementation packages the same formula as a linear map between proof-bearing
class functions. Sweep III retains only the displayed function on group
elements; invariance under conjugation and preservation of the
virtual-character lattice are result clauses. -/
noncomputable def inducedGeneralizedCharacterData
    {G : Type v} [Group G] [Fintype G] (H : Subgroup G)
    (φ : ClassFunctionData H ℂ) : G → ℂ := by
  classical
  exact fun g =>
    (Nat.card H : ℂ)⁻¹ *
      ∑ x : G,
        if hx : x⁻¹ * g * x ∈ H then
          φ.eval ⟨x⁻¹ * g * x, hx⟩
        else
          0

end LeanCategories.Algebra
