/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Weakly effaceable functors and the Yoneda defect functor

Weibel, *An Introduction to Homological Algebra* (1994), §1.6,
FC05-C01-U064.

For a fixed short exact sequence `0 → A → B → C → 0`, Weibel defines the
contravariant functor `W` objectwise by
`W(M) = coker(Hom(M,B) → Hom(M,C))`. Separately, a contravariant functor `F`
is weakly effaceable when every element of `F(M)` is killed after pullback
along some epimorphism `P → M`.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- A contravariant abelian-group-valued functor is weakly effaceable if every element
is killed after pullback along some epimorphism. -/
def WeaklyEffaceable (F : Aᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ (M : A) (x : F.obj (op M)), ∃ (P : A) (p : P ⟶ M), Epi p ∧ F.map p.op x = 0

/-- The Yoneda defect functor `W` associated to a short exact sequence
`0 → A → B → C → 0`: the cokernel of `h_B → h_C`. -/
noncomputable def yonedaDefect (S : ShortComplex A) : Aᵒᵖ ⥤ AddCommGrpCat.{v} :=
  cokernel ((preadditiveYoneda : A ⥤ Aᵒᵖ ⥤ AddCommGrpCat.{v}).map S.g)

/-- The canonical map `h_C → W` for the Yoneda defect functor. -/
noncomputable def yonedaDefectπ (S : ShortComplex A) :
    (preadditiveYoneda : A ⥤ Aᵒᵖ ⥤ AddCommGrpCat.{v}).obj S.X₃ ⟶ yonedaDefect S :=
  cokernel.π _

-- Intended boundary: the zero functor is weakly effaceable using the identity epimorphism.
example : WeaklyEffaceable ((Functor.const Aᵒᵖ).obj (0 : AddCommGrpCat.{v})) := by
  intro M x
  refine ⟨M, 𝟙 M, inferInstance, ?_⟩
  have hz : IsZero (((Functor.const Aᵒᵖ).obj (0 : AddCommGrpCat.{v})).obj (op M)) := by
    simpa using (isZero_zero AddCommGrpCat.{v})
  have hs : Subsingleton (((Functor.const Aᵒᵖ).obj (0 : AddCommGrpCat.{v})).obj (op M)) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  have hx : x = 0 := @Subsingleton.elim _ hs x 0
  simp [hx]

-- Separating boundary: a nonzero constant functor cannot be weakly effaceable because every
-- transition map is the identity and therefore cannot kill `1`.
example [Nonempty A] :
    ¬ WeaklyEffaceable ((Functor.const Aᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ))) := by
  intro h
  let M : A := Classical.choice (inferInstance : Nonempty A)
  obtain ⟨P, p, hp, hx⟩ := h M (ULift.up (1 : ℤ))
  have hne : (ULift.up (1 : ℤ) : ULift.{v} ℤ) ≠ 0 := by
    intro hz
    exact one_ne_zero (congrArg ULift.down hz)
  exact hne (by simpa using hx)

end LeanCategories.Homological
