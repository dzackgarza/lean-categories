/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CategoryGraph.Core.Universes
public import CategoryGraph.Core.Ids
public import CategoryGraph.Core.Classifier
public import CategoryGraph.Core.CategoricalPullback
public import CategoryGraph.Core.ClassifierReindexing
public import CategoryGraph.Core.Expr
public import CategoryGraph.Core.Normalize
public import CategoryGraph.Core.StructuralMap
public import CategoryGraph.Model.Atomic
public import CategoryGraph.Model.Interpretation
public import CategoryGraph.Registry.Entry
public import CategoryGraph.Registry.Extension
public import CategoryGraph.Presentation.Nodes
public import CategoryGraph.Categories.Algebra.Magmas
public import CategoryGraph.Categories.Algebra.Rings
public import CategoryGraph.Names.Standard
public import CategoryGraph.ForMathlib.CategoricalPullback

@[expose] public section

/-!
Standalone normalized category-graph root.

Mathlib realizations are **not** imported here; use
`CategoryGraph.Realization.Mathlib.Atomic` as a separate root.

This root contains no observation-specific correspondence data.
-/
