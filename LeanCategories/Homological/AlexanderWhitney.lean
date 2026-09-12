/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.DeltaZeroIter

/-!
# Alexander--Whitney components for a bisimplicial object

Weibel, *An Introduction to Homological Algebra* (1994), §8.5, pp. 276--277,
The Alexander--Whitney Map 8.5.4 (FC05-C08-U056).

For `n = p + q`, Weibel's Alexander--Whitney component

`f_{p,q} : A_{n,n} ⟶ A_{p,q}`

is obtained by retaining the first `p + 1` vertices in the horizontal
simplicial direction and the last `q + 1` vertices in the vertical direction.
Equivalently, it is the composite

`(∂ᵍ_{p+1} ⋯ ∂ᵍ_n) ≫ (∂ᵛ_0)^p`.

This file records that chain-level construction.  The assertions that these
components assemble to a chain map, induce the Eilenberg--Zilber isomorphism,
and admit the shuffle map as a chain-homotopy inverse are result-level content.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial

universe v u

variable {C : Type u} [Category.{v} C]

/-- The order-preserving inclusion of the first `p + 1` vertices of
`[p+q]`.  Contravariantly, a simplicial object sends it to the iterated last
face map `∂_{p+1} ⋯ ∂_{p+q}`. -/
def alexanderWhitneyFrontInclusion (p q : ℕ) : ⦋p⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i => Fin.castLE (by omega) i
      monotone' := fun _ _ h => h }

/-- Weibel's Alexander--Whitney component
`f_{p,q} : A_{p+q,p+q} ⟶ A_{p,q}`.

The first factor keeps the front `p`-simplex horizontally.  The second is
Mathlib's iteration of the zero face, which keeps the back `q`-simplex
vertically. -/
def alexanderWhitneyComponent
    (A : SimplicialObject (SimplicialObject C)) (p q : ℕ) :
    (A.obj (op ⦋p + q⦌)).obj (op ⦋p + q⦌) ⟶
      (A.obj (op ⦋p⦌)).obj (op ⦋q⦌) :=
  (A.map (alexanderWhitneyFrontInclusion p q).op).app (op ⦋p + q⦌) ≫
    (A.obj (op ⦋p⦌)).δ₀Iter p (by omega)

end LeanCategories.Homological
