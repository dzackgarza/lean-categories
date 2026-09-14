/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SimplicialChainComplexes
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# The degenerate subcomplex of a simplicial module

Weibel, *An Introduction to Homological Algebra* (1994), §8.3, pp. 263--269
(FC05-C08-U033).

For a simplicial module `A`, the degenerate part in degree `n` is the sum of
the images of the degeneracies `σ_i : A_{n-1} → A_n`.  Mathlib's Dold--Kan
development explicitly leaves this subcomplex as a TODO; this file records the
source degree submodules and the definition-layer realization of them as a
subcomplex of the unnormalized alternating-face complex.  The decomposition
`C(A)=N(A)⊕D(A)` is the following theorem row and is not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial
open AlgebraicTopology DoldKan

universe u v

variable (R : Type u) [Ring R]

/-- The degree-`n` degenerate submodule
`D_n(A)=Σ_{i=0}^{n-1} im(σ_i)`.  For `n=0` the index type is empty, hence this
is the zero submodule. -/
def simplicialDegenerateSubmodule
    (A : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    Submodule R (A.obj (op ⦋n⦌)) := by
  cases n with
  | zero => exact ⊥
  | succ n => exact ⨆ i : Fin (n + 1), LinearMap.range (A.σ i).hom

/-- The degreewise image of the Dold--Kan complementary projector `Q∞`. -/
def simplicialDegenerateRange
    (A : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    Submodule R (A.obj (op ⦋n⦌)) :=
  LinearMap.range ((QInfty (X := A)).f n).hom

/-- The `Q∞` image is exactly the sum of degeneracy images.  This packages the
two Dold--Kan facts needed for Weibel's `D_n(A)`: `decomposition_Q` expresses
`Q∞` as a sum through degeneracies, while `σ_i ≫ P∞ = 0` and
`P∞ + Q∞ = 1` show every degeneracy is fixed by `Q∞`. -/
lemma simplicialDegenerateRange_eq
    (A : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    simplicialDegenerateRange R A n = simplicialDegenerateSubmodule R A n := by
  cases n with
  | zero =>
      simp [simplicialDegenerateRange, simplicialDegenerateSubmodule, QInfty_f_0]
  | succ n =>
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        have hQ :
            (QInfty.f (n + 1) : A.obj (op ⦋n + 1⦌) ⟶ A.obj (op ⦋n + 1⦌)) =
              ∑ i : Fin (n + 1),
                (P i).f (n + 1) ≫ A.δ i.rev.succ ≫ A.σ (Fin.rev i) := by
          rw [QInfty_f, decomposition_Q n (n + 1)]
          rw [Finset.filter_eq_self.2]
          intro i hi
          exact i.isLt
        rw [show simplicialDegenerateSubmodule R A (n + 1) =
            ⨆ i : Fin (n + 1), LinearMap.range (A.σ i).hom by
              rfl]
        rw [show ((QInfty (X := A)).f (n + 1)).hom y =
            (∑ i : Fin (n + 1),
              ((P i).f (n + 1) ≫ A.δ i.rev.succ ≫ A.σ (Fin.rev i))).hom y by
              rw [hQ]]
        simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
        change (∑ i : Fin (n + 1),
          ((P i).f (n + 1) ≫ A.δ i.rev.succ ≫ A.σ (Fin.rev i)) y) ∈
            (⨆ i : Fin (n + 1), LinearMap.range (A.σ i).hom :
              Submodule R (A.obj (op ⦋n + 1⦌)))
        apply Submodule.sum_mem
        intro i hi
        apply (le_iSup (fun j : Fin (n + 1) => LinearMap.range (A.σ j).hom) (Fin.rev i))
        exact ⟨((P i).f (n + 1) ≫ A.δ i.rev.succ) y, rfl⟩
      · rw [show simplicialDegenerateSubmodule R A (n + 1) =
            ⨆ i : Fin (n + 1), LinearMap.range (A.σ i).hom by
              rfl]
        refine iSup_le fun i => ?_
        rintro x ⟨y, rfl⟩
        refine ⟨A.σ i y, ?_⟩
        have hPQ := PInfty_f_add_QInfty_f (X := A) (n + 1)
        change PInfty.f (n + 1) + QInfty.f (n + 1) =
          𝟙 (A.obj (op ⦋n + 1⦌)) at hPQ
        have hσP := σ_comp_PInfty A i
        have hfix : A.σ i ≫ (QInfty (X := A)).f (n + 1) = A.σ i := by
          calc
            A.σ i ≫ (QInfty (X := A)).f (n + 1) =
                0 + A.σ i ≫ (QInfty (X := A)).f (n + 1) := by rw [zero_add]
            _ = A.σ i ≫ PInfty.f (n + 1) + A.σ i ≫ QInfty.f (n + 1) := by
              rw [hσP]
            _ = A.σ i ≫ (PInfty.f (n + 1) + QInfty.f (n + 1)) := by
              rw [Preadditive.comp_add]
            _ = A.σ i ≫ 𝟙 _ := by rw [hPQ]
            _ = A.σ i := Category.comp_id _
        simpa only [ConcreteCategory.comp_apply] using congr($(hfix) y)

/-- Weibel's degenerate subcomplex `D(A)`, constructed as the categorical
image of the chain endomorphism `Q∞ : C(A) ⟶ C(A)`.  Since `Q∞` is already a
chain map, the image is automatically a chain subcomplex; no separate
differential or simplicial-identity proof is required here. -/
noncomputable abbrev simplicialDegenerateComplex
    (A : SimplicialObject (ModuleCat.{v} R)) : ChainComplex (ModuleCat.{v} R) ℕ :=
  Abelian.image (QInfty (X := A))

/-- The canonical inclusion `D(A) ↪ C(A)`. -/
noncomputable def simplicialDegenerateInclusion
    (A : SimplicialObject (ModuleCat.{v} R)) :
    simplicialDegenerateComplex R A ⟶ simplicialUnnormalizedChainComplex A :=
  Abelian.image.ι (QInfty (X := A))

/-- In each degree, the categorical image subcomplex is canonically the
linear-algebraic range of `Q∞_n`. -/
noncomputable def simplicialDegenerateDegreeIso
    (A : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    (simplicialDegenerateComplex R A).X n ≅
      ModuleCat.of R (simplicialDegenerateRange R A n) :=
  Abelian.PreservesImage.iso
      (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n)
      (QInfty (X := A)) ≪≫
    Abelian.imageIsoImage ((QInfty (X := A)).f n) ≪≫
    ModuleCat.imageIsoRange ((QInfty (X := A)).f n)

/-- Backwards-compatible name for the realized object.  The realization is
the canonical complex itself, not a structure with caller-supplied data. -/
abbrev SimplicialDegenerateSubcomplexRealization
    (_A : SimplicialObject (ModuleCat.{v} R)) := ChainComplex (ModuleCat.{v} R) ℕ

/-- The canonical realization of FC05-C08-U033. -/
noncomputable def simplicialDegenerateSubcomplexRealization
    (A : SimplicialObject (ModuleCat.{v} R)) :
    SimplicialDegenerateSubcomplexRealization R A :=
  simplicialDegenerateComplex R A

/-- Source-facing degree identification with `D_n(A)=Σ_i im(σ_i)`. -/
noncomputable def simplicialDegenerateComplexDegreeIso
    (A : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    (simplicialDegenerateComplex R A).X n ≅
      ModuleCat.of R (simplicialDegenerateSubmodule R A n) := by
  rw [← simplicialDegenerateRange_eq R A n]
  exact simplicialDegenerateDegreeIso R A n

set_option backward.isDefEq.respectTransparency false in
/-- Under the degree identification with `range(Q∞_n)`, the subcomplex
inclusion is the ordinary subtype map. -/
lemma simplicialDegenerateDegreeIso_hom_subtype
    (A : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    (simplicialDegenerateDegreeIso R A n).hom ≫
        ModuleCat.ofHom (Submodule.subtype (simplicialDegenerateRange R A n)) =
      (simplicialDegenerateInclusion R A).f n := by
  unfold simplicialDegenerateDegreeIso simplicialDegenerateInclusion
  simp only [Iso.trans_hom, Category.assoc]
  change
    (Abelian.PreservesImage.iso
        (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n)
        (QInfty (X := A))).hom ≫
      (Abelian.imageIsoImage ((QInfty (X := A)).f n)).hom ≫
      (ModuleCat.imageIsoRange ((QInfty (X := A)).f n)).hom ≫
      ModuleCat.ofHom (LinearMap.range ((QInfty (X := A)).f n).hom).subtype =
        (Abelian.image.ι (QInfty (X := A))).f n
  rw [ModuleCat.imageIsoRange_hom_subtype,
    Abelian.imageIsoImage_hom_comp_image_ι]
  exact Abelian.PreservesImage.iso_hom_ι
    (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n)
    (QInfty (X := A))

end LeanCategories.Homological
