/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.ClassifyingSpaceCyclicOperator
public import LeanCategories.Homological.TsyganBicomplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.Finsupp.Basic

/-!
# Hochschild and cyclic homology notation for a group

Weibel, *An Introduction to Homological Algebra* (1994), §9.7, pp. 338--343
(FC05-C09-U100).

For the cyclic `k`-module `kBG`, Weibel writes

* `HH_n(G) = HH_n(kBG)`, and
* `HC_n(G) = HC_n(kBG)`.

The source then identifies `HH_n(G)` with the ordinary homology of `BG`, and
hence with group homology `H_n(G;k)`.  Those comparison isomorphisms are
result-level content.  This file records only the cyclic-module realization
and the two notational definitions.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial

universe u

variable (k : Type u) [CommRing k]
variable (G : Type u) [Group G]

/-- A realization of Weibel's cyclic `k`-module `kBG`.

In simplicial degree `n`, the underlying `k`-module is the free module on
`G^n`.  The `cyclic_basis` field fixes the cyclic operator on the standard
basis to be the rotation from Example 9.6.2.

Source: Weibel, §9.7, pp. 338--343 (FC05-C09-U100), using Example 9.6.2. -/
structure GroupCyclicModuleRealization where
  /-- The realized cyclic `k`-module. -/
  obj : CyclicObject (C := ModuleCat.{u} k)
  /-- Degree `n` is the free `k`-module on `G^n`. -/
  degreeIso : ∀ n : ℕ,
    obj.obj.obj (op ⦋n⦌) ≅ ModuleCat.of k ((Fin n → G) →₀ k)
  /-- The cyclic operator agrees with Weibel's cyclic structure on `BG`. -/
  cyclic_basis : ∀ (n : ℕ) (a : Fin n → G),
    (degreeIso n).hom
        ((obj.t n).hom ((degreeIso n).inv (Finsupp.single a 1))) =
      Finsupp.single (classifyingSpaceCyclicData G n a) 1

/-- Weibel's notation `HH_n(G) := HH_n(kBG)` for a chosen realization of
the cyclic module `kBG`.

The comparison with ordinary group homology is theorem-layer content. -/
def groupHochschildHomology
    (A : GroupCyclicModuleRealization k G) (n : ℕ) : ModuleCat k :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).obj
    (cyclicHochschildComplex A.obj)

/-- Weibel's notation `HC_n(G) := HC_n(kBG)` for a chosen realization of
the cyclic module `kBG`. -/
def groupCyclicHomology
    (A : GroupCyclicModuleRealization k G)
    (T : TsyganBicomplexRealization A.obj)
    [HomologicalComplex₂.HasTotal T.bicomplex (ComplexShape.down ℕ)]
    (n : ℕ) : ModuleCat k :=
  cyclicHomology A.obj T n

end LeanCategories.Homological
