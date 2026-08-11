module

@[expose] public section

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Stable identity types

Stable IDs are normalized mathematical identity (matching the Python semantic seed /
authored ledger). They never embed Lean universe metavariables.
-/

namespace LeanCategories

/-- Stable category id, e.g. `cat.sets`, `cat.commutative_rings`. -/
structure CategoryId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable classifier id, e.g. `clf.magmas.commutative`. -/
structure ClassifierId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable category-family id (parameterized constructors), e.g. `fam.modules`. -/
structure CategoryFamilyId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of a parameter variable in a category-family expression. -/
structure ParameterId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of an operation on symbolic parameters. -/
structure ParameterOperationId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of a category-family parameter kind. -/
structure ParameterKindId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of a category-family variance declaration. -/
structure VarianceId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable constructor id, e.g. `ctor.hom_categories`. -/
structure ConstructorId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable functor id. -/
structure FunctorId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable structural port id, e.g. `port.multiplicative`. -/
structure PortId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable alias id, e.g. `alias.crings`. -/
structure AliasId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable route selector for multi-port refinements. -/
structure RouteId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable refinement occurrence id (for projection certificates). -/
structure RefinementId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable structural theorem id. -/
structure StructuralTheoremId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable opaque structural port id. -/
structure OpaquePortId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable cone / finite-limit certificate id. -/
structure ConeCertificateId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable coherence-witness id. -/
structure CoherenceId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable presentation-overlay id. -/
structure PresentationId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable cluster id for presentation overlay only. -/
structure ClusterId where
  raw : String
  deriving DecidableEq, Repr, Hashable

instance : Inhabited CategoryId := ⟨⟨""⟩⟩
instance : Inhabited ClassifierId := ⟨⟨""⟩⟩
instance : Inhabited CategoryFamilyId := ⟨⟨""⟩⟩
instance : Inhabited ParameterId := ⟨⟨""⟩⟩
instance : Inhabited ParameterOperationId := ⟨⟨""⟩⟩
instance : Inhabited ParameterKindId := ⟨⟨""⟩⟩
instance : Inhabited VarianceId := ⟨⟨""⟩⟩
instance : Inhabited PortId := ⟨⟨""⟩⟩
instance : Inhabited AliasId := ⟨⟨""⟩⟩
instance : Inhabited RouteId := ⟨⟨""⟩⟩
instance : Inhabited OpaquePortId := ⟨⟨""⟩⟩

end LeanCategories
