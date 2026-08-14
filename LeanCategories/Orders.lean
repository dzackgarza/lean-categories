/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Ordered-category routes

Mathlib owns the categories of preorders, partial orders, linear orders, and
lattices. Their morphisms are monotone maps for the first three categories and
lattice homomorphisms for `Lat`. This module exposes the canonical definitions.
-/

public import Mathlib.Order.Category.Preord
public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Category.LinOrd
public import Mathlib.Order.Category.Lat

@[expose] public section
