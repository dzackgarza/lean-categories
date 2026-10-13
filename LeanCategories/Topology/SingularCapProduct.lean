/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Singular cap-product formula data

Definition-level realization of Hatcher `FC07-C03-U050`, ported from the
checked ATLAS chain-level construction.

Sweep III records only the raw chain operation.  For a degree-`p` cochain and
a singular `(p+q)`-simplex, it evaluates the cochain on the front `p`-face and
uses the resulting scalar to multiply the back `q`-face.  The signed boundary
identity, relative descent, and passage to homology/cohomology are result-layer
statements and are deliberately absent here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open CategoryTheory
open AlgebraicTopology

open Simplicial in
/-- Inclusion of the front `p`-face in a `(p+q)`-simplex. -/
def singularCapFrontFace (p q : ℕ) :
    (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun i => Fin.castLE (by omega) i, fun _ _ h => h⟩

open Simplicial in
/-- Inclusion of the back `q`-face in a `(p+q)`-simplex. -/
def singularCapBackFace (p q : ℕ) :
    (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun j => ⟨j.val + p, by omega⟩,
    fun a b (h : a ≤ b) => show a.val + p ≤ b.val + p by omega⟩

/-- The singular chain complex `C_*(X;R)`. -/
abbrev singularCapChainComplex (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X

/-- Singular `n`-simplices of `X`. -/
abbrev singularCapSimplices (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

open CategoryTheory.Limits Simplicial in
/-- Hatcher's raw chain-level cap product.

For `β : C_p(X;R) ⟶ R`, the image of a generator `σ` of degree `p+q`
is `β(σ|front) • (σ|back)`.  `Sigma.desc` extends this basis formula to
the free singular-chain module without adding any descent or chain-map law. -/
def singularCapProductChainMap (R : Type) [CommRing R] (X : TopCat.{0})
    (p q : ℕ) (β : (singularCapChainComplex R X).X p ⟶ ModuleCat.of R R) :
    (singularCapChainComplex R X).X (p + q) ⟶
      (singularCapChainComplex R X).X q :=
  Sigma.desc (fun (σ : singularCapSimplices X (p + q)) =>
    let σFront : singularCapSimplices X p :=
      (TopCat.toSSet.obj X).map (singularCapFrontFace p q).op σ
    let σBack : singularCapSimplices X q :=
      (TopCat.toSSet.obj X).map (singularCapBackFace p q).op σ
    (Sigma.ι (fun (_ : singularCapSimplices X p) => ModuleCat.of R R) σFront ≫ β) ≫
      Sigma.ι (fun (_ : singularCapSimplices X q) => ModuleCat.of R R) σBack)

end LeanCategories.Topology
