/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Typed

@[expose] public section

/-!
# Stable exported identifiers

The registry extension checks declaration names against the Lean environment
before it persists a row. These identifiers are typed views of those checked
rows. They do not introduce a second registry or turn a name into a semantic
object.

Lean's `Name` is the stable declaration key used by environment extensions and
by the declaration quotation syntax. Mathlib uses the same key for declaration
lookup and metadata. The registry's typed rows supply the semantic evidence.
-/

namespace LeanCategories

open CategoryTheory

/-! ## Identifier kinds -/

/-- An exported category declaration with its normalized category identity. -/
structure ExportedCategoryIdentifier where
  id : CategoryId
  declaration : Lean.Name
  deriving DecidableEq, Repr, Inhabited

/--
An exported functor declaration.

The category-expression indices preserve the source and target endpoints in
the type. They cannot be replaced by endpoint strings without losing typing.
-/
structure ExportedFunctorIdentifier (source target : CategoryExpr) where
  id : FunctorId
  declaration : Lean.Name
  deriving DecidableEq, Repr

/-!
An exported standard object is identified by the public declaration that
defines it. Its declaration name is the identity; no generated numeric ID or
second spelling is introduced.

The constructors below create these identifiers only from typed registry rows.
Thus the resulting name is one already checked by the registry extension.
-/
structure ExportedStandardObjectIdentifier where
  declaration : Lean.Name
  deriving DecidableEq, Repr, Inhabited

/-- The kind of an exported declaration. -/
inductive ExportedIdentifier
  | category (identifier : ExportedCategoryIdentifier)
  | functor {source target : CategoryExpr}
      (identifier : ExportedFunctorIdentifier source target)
  | standardObject (identifier : ExportedStandardObjectIdentifier)
  deriving Repr

namespace TypedCategoryEntry

/-- The stable exported identifier of a checked category row. -/
def exportedIdentifier (entry : TypedCategoryEntry) : ExportedCategoryIdentifier :=
  { id := entry.id, declaration := entry.declaration }

/--
View the checked category declaration as an exported standard object.

This is a view of the same declaration, not a second registry row.
-/
def standardObjectIdentifier (entry : TypedCategoryEntry) :
    ExportedStandardObjectIdentifier :=
  { declaration := entry.declaration }

end TypedCategoryEntry

namespace TypedFunctorEntry

/-- The stable exported identifier of a checked functor row. -/
def exportedIdentifier (entry : TypedFunctorEntry) :
    ExportedFunctorIdentifier entry.metadata.source entry.metadata.target :=
  { id := entry.id, declaration := entry.declaration }

/--
View the checked functor declaration as an exported standard object.

This is a view of the same declaration, not a second registry row.
-/
def standardObjectIdentifier (entry : TypedFunctorEntry) :
    ExportedStandardObjectIdentifier :=
  { declaration := entry.declaration }

end TypedFunctorEntry

namespace ExportedIdentifier

/-- The Lean declaration name carried by an exported identifier. -/
def declaration : ExportedIdentifier → Lean.Name
  | .category identifier => identifier.declaration
  | .functor identifier => identifier.declaration
  | .standardObject identifier => identifier.declaration

end ExportedIdentifier

/-! ## The typed views retain the registry identities exactly. -/

theorem TypedCategoryEntry.exportedIdentifier_id (entry : TypedCategoryEntry) :
    entry.exportedIdentifier.id = entry.id := rfl

theorem TypedCategoryEntry.exportedIdentifier_declaration (entry : TypedCategoryEntry) :
    entry.exportedIdentifier.declaration = entry.declaration := rfl

theorem TypedFunctorEntry.exportedIdentifier_id (entry : TypedFunctorEntry) :
    entry.exportedIdentifier.id = entry.id := rfl

theorem TypedFunctorEntry.exportedIdentifier_declaration (entry : TypedFunctorEntry) :
    entry.exportedIdentifier.declaration = entry.declaration := rfl

end LeanCategories
