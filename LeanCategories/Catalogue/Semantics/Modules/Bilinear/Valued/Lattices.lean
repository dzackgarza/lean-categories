/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public import LeanCategories.Lattices.Integral
public import LeanCategories.Lattices.Valued.Standard
public import LeanCategories.Catalogue.Semantics.Lattices.Valued.CatalogueRegistration
public meta import LeanCategories.Catalogue.Semantics.Lattices.Valued.Catalogue
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Catalogue

@[expose] public section

/-!
# Named lattices

Objects and morphisms of `BilWForm(ℤ)` (`cat.bil_wform`), from `LeanCategories.Lattices.Integral`:

* `A(n)`: the root lattice `A_n` on its simple roots `αᵢ = eᵢ − eᵢ₊₁ ∈ ℤ^{n+1}`;
* `A_dual(n)`: its dual `A_n^♯ ⊆ ℚⁿ`, with values in `ℚ`;
* `to_dual(n) : A(n) → A_dual(n)`: the inclusion `A_n ⊆ A_n^♯`, whose cokernel is the
  discriminant group.
-/

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.bil_wform.root_lattice_a"⟩, category := CategoryId.bilWForm, name := "A"
    declaration := `LeanCategories.Lattices.Integral.rootA }

normalized_registry .object
  { id := ⟨"obj.bil_wform.root_lattice_a_dual"⟩, category := CategoryId.bilWForm, name := "A_dual"
    declaration := `LeanCategories.Lattices.Integral.rootADual }

normalized_registry .morphism
  { id := ⟨"mor.bil_wform.root_lattice_a_to_dual"⟩, category := CategoryId.bilWForm
    name := "to_dual", declaration := `LeanCategories.Lattices.Integral.rootAToDual }

-- The existing integral E₈ lattice retains its Gram form and selected ℤ-module.
normalized_registry .object
  { id := ⟨"obj.integral_lattice.e8"⟩, category := CategoryId.integralLattice, name := "E8"
    declaration := `LeanCategories.Lattices.Valued.e8Lattice }

end CasCatalogue
