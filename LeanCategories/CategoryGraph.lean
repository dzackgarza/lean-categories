/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryGraph.Core.Universes
public import LeanCategories.CategoryGraph.Core.Ids
public import LeanCategories.CategoryGraph.Core.Classifier
public import LeanCategories.CategoryGraph.Core.CategoricalPullback
public import LeanCategories.CategoryGraph.Core.ClassifierReindexing
public import LeanCategories.CategoryGraph.Core.Expr
public import LeanCategories.CategoryGraph.Core.Normalize
public import LeanCategories.CategoryGraph.Core.StructuralMap
public import LeanCategories.CategoryGraph.Model.Atomic
public import LeanCategories.CategoryGraph.Model.Interpretation
public import LeanCategories.CategoryGraph.Registry.Entry
public import LeanCategories.CategoryGraph.Registry.Extension
public import LeanCategories.CategoryGraph.Presentation.Nodes
public import LeanCategories.CategoryGraph.Categories.Algebra.Magmas
public import LeanCategories.CategoryGraph.Categories.Algebra.Rings
public import LeanCategories.CategoryGraph.Names.Standard
public import LeanCategories.CategoryGraph.ForMathlib.CategoricalPullback

@[expose] public section

/-!
Standalone normalized category-graph root.

Mathlib realizations are **not** imported here; use
`CategoryGraph.Realization.Mathlib.Atomic` as a separate root.

This root contains no observation-specific correspondence data.
-/
