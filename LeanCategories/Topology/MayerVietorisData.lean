/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Integral Mayer--Vietoris data

Definition-level realization of Hatcher FC07-C02-U067, following the pinned
`sphere-six-complex` binary-open-cover implementation.

For an open cover `U ⊔ V = ⊤`, the two ordinary maps in the integral
Mayer--Vietoris sequence are the alternating map

`H_n(U ∩ V) → H_n(U) ⊕ H_n(V)`

and the sum of the two inclusion maps

`H_n(U) ⊕ H_n(V) → H_n(X)`.

Sweep III constructs those maps and records the exact source graph for a
connecting family `H_{n+1}(X) → H_n(U ∩ V)`.  Valid Mayer--Vietoris data are
boundary families carrying that exact graph; no arbitrary family is selected
before the cover-chain/excision theorem.  Construction of the connecting
homomorphism and exactness remain Sweep-IV result work.
-/

@[expose] public noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace LeanCategories.Topology

/-- Integral singular homology as a functor on topological spaces. -/
abbrev integralSingularHomologyFunctorData (n : ℕ) :
    TopCat.{0} ⥤ AddCommGrpCat.{0} :=
  (singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)

/-- The alternating intersection-to-pieces map in the integral
Mayer--Vietoris sequence. -/
def integralMVToBiprodData {X : TopCat.{0}}
    (U V : Opens X) (n : ℕ) :
    (integralSingularHomologyFunctorData n).obj
        ((Opens.toTopCat X).obj (U ⊓ V)) ⟶
      (integralSingularHomologyFunctorData n).obj
          ((Opens.toTopCat X).obj U) ⊞
        (integralSingularHomologyFunctorData n).obj
          ((Opens.toTopCat X).obj V) :=
  biprod.lift
    ((integralSingularHomologyFunctorData n).map
      ((Opens.toTopCat X).map (Opens.infLELeft U V)))
    (-((integralSingularHomologyFunctorData n).map
      ((Opens.toTopCat X).map (Opens.infLERight U V))))

/-- The sum of the two piece-inclusion maps in the integral
Mayer--Vietoris sequence. -/
def integralMVFromBiprodData {X : TopCat.{0}}
    (U V : Opens X) (n : ℕ) :
    (integralSingularHomologyFunctorData n).obj
          ((Opens.toTopCat X).obj U) ⊞
        (integralSingularHomologyFunctorData n).obj
          ((Opens.toTopCat X).obj V) ⟶
      (integralSingularHomologyFunctorData n).obj X :=
  biprod.desc
    ((integralSingularHomologyFunctorData n).map (Opens.inclusion' U))
    ((integralSingularHomologyFunctorData n).map (Opens.inclusion' V))

/-- Type of the connecting-family data in a binary integral
Mayer--Vietoris sequence. -/
abbrev IntegralMayerVietorisBoundaryData {X : TopCat.{0}}
    (U V : Opens X) :=
  ∀ n : ℕ,
    (integralSingularHomologyFunctorData (n + 1)).obj X ⟶
      (integralSingularHomologyFunctorData n).obj
        ((Opens.toTopCat X).obj (U ⊓ V))

/-- Exact graph of Hatcher's binary-open-cover Mayer--Vietoris sequence.

The cover hypothesis is explicit, but no exactness proof is constructed here.
The three conjuncts are the recurring exactness positions in the long
sequence. -/
def IsIntegralMayerVietorisBoundaryData {X : TopCat.{0}}
    (U V : Opens X) (_hcover : U ⊔ V = ⊤)
    (boundary : IntegralMayerVietorisBoundaryData U V) : Prop :=
  ∀ n : ℕ,
    Function.Exact
        (fun x ↦ boundary n x)
        (fun x ↦ integralMVToBiprodData U V n x) ∧
      Function.Exact
        (fun x ↦ integralMVToBiprodData U V n x)
        (fun x ↦ integralMVFromBiprodData U V n x) ∧
      Function.Exact
        (fun x ↦ integralMVFromBiprodData U V (n + 1) x)
        (fun x ↦ boundary n x)

/-- Source-faithful integral Mayer--Vietoris data: a connecting family
together with Hatcher's exact long-sequence graph.  The cover-chain/excision
theorem supplies existence later. -/
abbrev IntegralMayerVietorisData {X : TopCat.{0}}
    (U V : Opens X) (hcover : U ⊔ V = ⊤) :=
  {boundary : IntegralMayerVietorisBoundaryData U V //
    IsIntegralMayerVietorisBoundaryData U V hcover boundary}

end LeanCategories.Topology
