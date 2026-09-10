/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

@[expose] public noncomputable section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

universe u

variable (k : Type u) [Field k]

/-- A finite affine combination of elements of `X`: finitely supported coefficients whose
sum is one. This is the endofunctor underlying Riehl's affine-combination monad in
FC03-C05-U012. -/
structure AffineCombination (X : Type u) where
  /-- The finitely supported coefficient function. -/
  weights : X →₀ k
  /-- Affine coefficients have total mass one. -/
  total : weights.sum (fun _ a => a) = 1

namespace AffineCombination

variable {k : Type u} [Field k]
variable {X Y Z : Type u}

@[ext]
theorem ext {a b : AffineCombination k X} (h : a.weights = b.weights) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The point mass at `x`. -/
noncomputable def pure (x : X) : AffineCombination k X where
  weights := Finsupp.single x 1
  total := by simp

/-- Push an affine combination forward along a function. -/
noncomputable def map (f : X → Y) (a : AffineCombination k X) : AffineCombination k Y where
  weights := a.weights.mapDomain f
  total := by simpa [Finsupp.sum_mapDomain_index] using a.total

@[simp]
theorem map_id (a : AffineCombination k X) : map id a = a := by
  apply ext
  simp [map]

@[simp]
theorem map_comp (a : AffineCombination k X) (f : X → Y) (g : Y → Z) :
    map g (map f a) = map (g ∘ f) a := by
  apply ext
  simp [map, Finsupp.mapDomain_comp]

@[simp]
theorem map_pure (f : X → Y) (x : X) : map f (pure (k := k) x) = pure (f x) := by
  apply ext
  simp [map, pure]

/-- Flatten an affine combination of affine combinations by multiplying outer and inner
coefficients. -/
noncomputable def flatten (a : AffineCombination k (AffineCombination k X)) :
    AffineCombination k X where
  weights := a.weights.sum (fun d r => r • d.weights)
  total := by
    rw [Finsupp.sum_sum_index]
    · calc
        a.weights.sum (fun d r => (r • d.weights).sum (fun _ x => x)) =
            a.weights.sum (fun _ r => r) := by
          apply Finsupp.sum_congr
          intro d hd
          rw [Finsupp.sum_smul_index]
          · change d.weights.sum (fun _ x => a.weights d * x) = a.weights d
            calc
              d.weights.sum (fun _ x => a.weights d * x) =
                  a.weights d * d.weights.sum (fun _ x => x) := by
                classical
                simp only [Finsupp.sum, Finset.mul_sum]
              _ = a.weights d := by rw [d.total, mul_one]
          · intro
            rfl
        _ = 1 := a.total
    · intro
      rfl
    · intro
      simp

@[simp]
theorem flatten_pure (x : AffineCombination k X) :
    flatten (pure (k := k) x) = x := by
  apply ext
  simp [flatten, pure]

@[simp]
theorem map_flatten (a : AffineCombination k (AffineCombination k X)) (g : X → Y) :
    map g (flatten a) = flatten (map (map g) a) := by
  apply ext
  simp [map, flatten, Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index,
    Finsupp.sum_smul_index, Finsupp.smul_sum]

@[simp]
theorem flatten_flatten
    (a : AffineCombination k (AffineCombination k (AffineCombination k X))) :
    flatten (flatten a) = flatten (map flatten a) := by
  apply ext
  simp [map, flatten, Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index,
    Finsupp.sum_smul_index, Finsupp.smul_sum, mul_smul]

@[simp]
theorem flatten_map_pure (a : AffineCombination k X) :
    flatten (map pure a) = a := by
  apply ext
  simp [map, flatten, pure, Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index]

end AffineCombination

/-- The affine-combination endofunctor on types. -/
noncomputable def affineCombinationFunctor : Type u ⥤ Type u where
  obj X := AffineCombination k X
  map f := TypeCat.ofHom (AffineCombination.map (k := k) (fun x => f x))
  map_id X := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext a
    change AffineCombination.map (k := k) id a = a
    exact AffineCombination.map_id a
  map_comp f g := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext a
    change AffineCombination.map (k := k) (fun x => g (f x)) a =
      AffineCombination.map (k := k) (fun y => g y)
        (AffineCombination.map (k := k) (fun x => f x) a)
    exact (AffineCombination.map_comp a (fun x => f x) (fun y => g y)).symm

/-- The affine-combination monad. Its multiplication forms the barycenter of a finite affine
combination of finite affine combinations. -/
noncomputable def affineCombinationMonad : Monad (Type u) where
  toFunctor := affineCombinationFunctor k
  η := {
    app := fun X => TypeCat.ofHom (AffineCombination.pure (k := k))
    naturality := by
      intro X Y f
      ext x
      exact (AffineCombination.map_pure (fun x => f x) x).symm
  }
  μ := {
    app := fun X => TypeCat.ofHom (AffineCombination.flatten (k := k))
    naturality := by
      intro X Y f
      ext a
      exact (AffineCombination.map_flatten a (fun x => f x)).symm
  }
  assoc := by
    intro X
    ext a
    exact (AffineCombination.flatten_flatten a).symm
  left_unit := by
    intro X
    ext a
    exact AffineCombination.flatten_pure a
  right_unit := by
    intro X
    ext a
    exact AffineCombination.flatten_map_pure a

/-- Riehl Definition 5.2.3 (FC03-C05-U012): an affine space over `k` in the monadic
presentation is an Eilenberg–Moore algebra for the affine-combination monad. -/
abbrev AffineCombinationAlgebra := (affineCombinationMonad k).Algebra

end LeanCategories.CategoryTheory
