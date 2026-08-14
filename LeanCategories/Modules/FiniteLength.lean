/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Filtration
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import LeanCategories.Modules.Mathlib

@[expose] public section

/-!
# Finite-length modules and standard chain constructions

This file routes Atiyah--Macdonald's chain-condition vocabulary to Mathlib.
It does not introduce alternate predicates or composition-series structures.
-/

namespace LeanCategories.Modules.Mathlib

open CategoryTheory

universe u w

variable (R : RingCat.{u})

/-- Modules of finite length, using Mathlib's `IsFiniteLength` predicate. -/
abbrev FiniteLengthModuleCat : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => IsFiniteLength R M)

/-- The canonical inclusion of finite-length modules into all modules. -/
abbrev finiteLengthInclusion : FiniteLengthModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => IsFiniteLength R M)

/-- A chain of submodules, in Mathlib's order-theoretic representation. -/
abbrev SubmoduleChain (M : ModuleCat.{w} R) :=
  ℕ →o Submodule R M

/-- A composition series of an `R`-module, using Mathlib's `CompositionSeries`. -/
abbrev ModuleCompositionSeries (M : ModuleCat.{w} R) :=
  CompositionSeries (Submodule R M)

/-- The length of an `R`-module, using Mathlib's `Module.length`. -/
abbrev moduleLength (M : ModuleCat.{w} R) : ℕ∞ :=
  Module.length R M

end LeanCategories.Modules.Mathlib

namespace LeanCategories.Algebra

universe u

variable (R : Type u) [CommRing R]

/-- An ideal filtration of an `R`-module, using Mathlib's `Ideal.Filtration`. -/
abbrev IdealFiltration (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :=
  Ideal.Filtration I M

/-- The `I`-adic topology, using Mathlib's canonical topology. -/
abbrev adicTopology (I : Ideal R) : TopologicalSpace R :=
  I.adicTopology

/-- The predicate that a topology is the `I`-adic topology. -/
abbrev IsAdicTopology [TopologicalSpace R] (I : Ideal R) : Prop :=
  IsAdic I

/-- The adic completion of an `R`-module, using Mathlib's canonical construction. -/
abbrev adicCompletion (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :=
  AdicCompletion I M

end LeanCategories.Algebra
