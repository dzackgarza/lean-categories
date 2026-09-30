/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Ports
public import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas

@[expose] public section

/-!
# Presentations of the commutativity property (CC-PROP)

* `is_commutative`, on any receiver with a structural route to magmas;
* `is_abelian`, the same classifier, available on groups only (#53 §12).

Deciding it is a leaf's contribution (a `Decider` for `clf.magmas.commutative`).
-/

namespace CasCatalogue

normalized_registry .property
  { id := ⟨"prop.is_commutative"⟩, name := "is_commutative"
    classifier := ClassifierId.magmasCommutative }
normalized_registry .property
  { id := ⟨"prop.is_abelian"⟩, name := "is_abelian", classifier := ClassifierId.magmasCommutative
    receiver := some Algebra.Catalogue.Magmas.Groups }

end CasCatalogue
