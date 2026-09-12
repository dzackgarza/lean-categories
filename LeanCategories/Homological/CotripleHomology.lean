/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CotripleResolution
public import LeanCategories.Homological.SimplicialChainComplexes

/-!
# Cotriple homology

Weibel, *An Introduction to Homological Algebra* (1994), Definition 8.7.1,
pp. 286--293 (FC05-C08-U075).

Construction 8.6.4 supplies the degree, face, and degeneracy formulas for the
canonical cotriple resolution.  The proof that those formulas satisfy the
simplicial identities is theorem-layer work, so here we package a realization
of those formulas by an actual simplicial object and define cotriple homology
from such a realization.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

namespace CategoryTheory.Comonad

universe u v

variable {C : Type u} [Category.{v} C]

/-- A simplicial realization of Weibel's canonical cotriple formulas.

The existence of this realization from the comonad laws is the result clause
of Construction 8.6.4 and is deliberately not proved in the Definitions sweep. -/
structure SimplicialResolution (T : Comonad C) (A : C) where
  /-- The realized simplicial object. -/
  obj : SimplicialObject C
  /-- Identification of degree `n` with `T^(n+1)(A)`. -/
  degreeIso : ∀ n : ℕ, obj.obj (op ⦋n⦌) ≅ T.simplicialDegree A n
  /-- Compatibility of the simplicial faces with the canonical cotriple faces. -/
  face_comm : ∀ (n : ℕ) (i : Fin (n + 2)),
    (degreeIso (n + 1)).hom ≫ T.face A (n + 1) i =
      obj.δ i ≫ (degreeIso n).hom
  /-- Compatibility of the simplicial degeneracies with the canonical cotriple degeneracies. -/
  degeneracy_comm : ∀ (n : ℕ) (i : Fin (n + 1)),
    (degreeIso n).hom ≫ T.degeneracy A n i =
      obj.σ i ≫ (degreeIso (n + 1)).hom

end CategoryTheory.Comonad

namespace LeanCategories.Homological

universe u v uD vD

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]

/-- Weibel's cotriple homology `H_n(A;E)=π_n E(T_*A)`, computed from a
simplicial realization of the canonical cotriple resolution. -/
noncomputable def cotripleHomology (T : Comonad C) (A : C)
    (S : T.SimplicialResolution A) (E : C ⥤ D) (n : ℕ) : D :=
  simplicialHomotopyObject (S.obj ⋙ E) n

end LeanCategories.Homological
