/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.DeltaZeroIter
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.GroupTheory.Perm.Sign

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

This file records that degreewise construction together with the explicit
signed shuffle components in the reverse direction. The assertions that the
two degreewise families assemble to chain maps, induce the Eilenberg--Zilber
isomorphism, and are chain-homotopy inverse are result-level content.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial
open scoped BigOperators

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

/-- A permutation of the (p+q) degeneracy positions is a ((p,q))-shuffle
when it preserves the order of the first (p) positions and separately the
last (q) positions. -/
def alexanderWhitneyIsShuffle (p q : ℕ)
    (σ : Equiv.Perm (Fin (p + q))) : Prop :=
  (∀ i j : Fin (p + q),
      i < j →
      (i : ℕ) < p →
      (j : ℕ) < p →
      σ i < σ j) ∧
  (∀ i j : Fin (p + q),
      i < j →
      p ≤ (i : ℕ) →
      p ≤ (j : ℕ) →
      σ i < σ j)

/-- For a permutation of the shuffle positions, the horizontal degeneracy
word is represented by the monotone surjection from `[p+q]` to `[p]` whose value
at a vertex counts first-block shuffle positions lying strictly before it. -/
def alexanderWhitneyShuffleHorizontalMap (p q : ℕ)
    (σ : Equiv.Perm (Fin (p + q))) : ⦋p + q⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j =>
        ⟨(Finset.univ.filter fun i : Fin p =>
            (σ (Fin.castAdd q i) : ℕ) < (j : ℕ)).card, by
          have hcard :
              (Finset.univ.filter fun i : Fin p =>
                (σ (Fin.castAdd q i) : ℕ) < (j : ℕ)).card ≤ p := by
            calc
              _ ≤ (Finset.univ : Finset (Fin p)).card :=
                Finset.card_filter_le _ _
              _ = p := Fintype.card_fin p
          omega⟩
      monotone' := by
        intro a b hab
        simp only [Fin.mk_le_mk]
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact lt_of_lt_of_le hi (Fin.le_iff_val_le_val.mp hab) }

/-- For a permutation of the shuffle positions, the vertical degeneracy word
is represented by the monotone surjection from `[p+q]` to `[q]` whose value at a
vertex counts second-block shuffle positions lying strictly before it. -/
def alexanderWhitneyShuffleVerticalMap (p q : ℕ)
    (σ : Equiv.Perm (Fin (p + q))) : ⦋p + q⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j =>
        ⟨(Finset.univ.filter fun i : Fin q =>
            (σ (Fin.natAdd p i) : ℕ) < (j : ℕ)).card, by
          have hcard :
              (Finset.univ.filter fun i : Fin q =>
                (σ (Fin.natAdd p i) : ℕ) < (j : ℕ)).card ≤ q := by
            calc
              _ ≤ (Finset.univ : Finset (Fin q)).card :=
                Finset.card_filter_le _ _
              _ = q := Fintype.card_fin q
          omega⟩
      monotone' := by
        intro a b hab
        simp only [Fin.mk_le_mk]
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact lt_of_lt_of_le hi (Fin.le_iff_val_le_val.mp hab) }

/-- The degeneracy term attached to one permutation in Weibel's shuffle
formula `A_{p,q} → A_{p+q,p+q}`. -/
def alexanderWhitneyShuffleTerm
    (A : SimplicialObject (SimplicialObject C)) (p q : ℕ)
    (σ : Equiv.Perm (Fin (p + q))) :
    (A.obj (op ⦋p⦌)).obj (op ⦋q⦌) ⟶
      (A.obj (op ⦋p + q⦌)).obj (op ⦋p + q⦌) :=
  (A.obj (op ⦋p⦌)).map (alexanderWhitneyShuffleVerticalMap p q σ).op ≫
    (A.map (alexanderWhitneyShuffleHorizontalMap p q σ).op).app (op ⦋p + q⦌)

/-- Weibel's reverse shuffle component in bidegree `(p,q)`: the signed sum
of the horizontal/vertical degeneracy terms indexed by `(p,q)`-shuffles.

The assertion that these degreewise maps assemble to a chain map is result
content and is not part of this declaration. -/
noncomputable def alexanderWhitneyShuffleComponent [Preadditive C]
    (A : SimplicialObject (SimplicialObject C)) (p q : ℕ) :
    (A.obj (op ⦋p⦌)).obj (op ⦋q⦌) ⟶
      (A.obj (op ⦋p + q⦌)).obj (op ⦋p + q⦌) := by
  classical
  exact ∑ σ : Equiv.Perm (Fin (p + q)),
    if alexanderWhitneyIsShuffle p q σ then
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        alexanderWhitneyShuffleTerm A p q σ
    else 0

end LeanCategories.Homological
