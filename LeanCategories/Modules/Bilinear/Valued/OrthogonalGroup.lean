/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Isometry
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]

namespace BilinModuleCat

/-- Form-preserving linear automorphisms of a formed module. -/
def orthogonalSubgroup (M : BilinModuleCat R W) :
    Subgroup (M.carrier ≃ₗ[R] M.carrier) where
  carrier f := ∀ x y, M.pairing (f x) (f y) = M.pairing x y
  one_mem' := fun _ _ ↦ rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    simpa using (hf (f.symm x) (f.symm y)).symm

/-- The orthogonal group of a formed module. -/
abbrev OrthogonalGroup (M : BilinModuleCat R W) :=
  orthogonalSubgroup M

namespace OrthogonalGroup

variable {M : BilinModuleCat R W}

/-- An isometry identifies the orthogonal groups of its source and target. -/
noncomputable def congr {N : BilinModuleCat R W} (e : M ≅ N) :
    OrthogonalGroup M ≃* OrthogonalGroup N where
  toFun g := by
    let f := linearEquivOfIso e
    refine ⟨f.symm.trans (g.1.trans f), ?_⟩
    intro x y
    change N.pairing (f (g.1 (f.symm x))) (f (g.1 (f.symm y))) = N.pairing x y
    rw [linearEquivOfIso_pairing e, g.property]
    simpa [f] using (linearEquivOfIso_pairing e (f.symm x) (f.symm y)).symm
  invFun g := by
    let f := linearEquivOfIso e
    refine ⟨f.trans (g.1.trans f.symm), ?_⟩
    intro x y
    change M.pairing (f.symm (g.1 (f x))) (f.symm (g.1 (f y))) = M.pairing x y
    calc
      _ = N.pairing (g.1 (f x)) (g.1 (f y)) := by
        simpa [f] using (linearEquivOfIso_pairing e
          (f.symm (g.1 (f x))) (f.symm (g.1 (f y)))).symm
      _ = N.pairing (f x) (f y) := g.property _ _
      _ = M.pairing x y := linearEquivOfIso_pairing e x y
  left_inv g := by
    let f := linearEquivOfIso e
    apply Subtype.ext
    ext x
    change f.symm (f (g.1 (f.symm (f x)))) = g.1 x
    simp
  right_inv g := by
    let f := linearEquivOfIso e
    apply Subtype.ext
    ext x
    change f (f.symm (g.1 (f (f.symm x)))) = g.1 x
    simp
  map_mul' g h := by
    let f := linearEquivOfIso e
    apply Subtype.ext
    ext x
    change f ((g.1 * h.1) (f.symm x)) =
      f (g.1 (f.symm (f (h.1 (f.symm x)))))
    simp

/-- An orthogonal-group element of a scalar-valued form as a Mathlib isometry. -/
def toMathlibIsometryEquiv {N : BilinModuleCat R R}
    (g : OrthogonalGroup N) :
    N.asBilinForm.IsometryEquiv N.asBilinForm where
  __ := g.1
  map_app' x y := g.property x y

/-- A Mathlib isometric equivalence as an orthogonal-group element. -/
def fromMathlibIsometryEquiv {N : BilinModuleCat R R}
    (g : N.asBilinForm.IsometryEquiv N.asBilinForm) :
    OrthogonalGroup N := by
  refine ⟨g.toLinearEquiv, ?_⟩
  intro x y
  exact g.map_app y x

@[simp]
theorem from_toMathlibIsometryEquiv {N : BilinModuleCat R R}
    (g : OrthogonalGroup N) :
    fromMathlibIsometryEquiv (toMathlibIsometryEquiv g) = g :=
  rfl

@[simp]
theorem to_fromMathlibIsometryEquiv
    {N : BilinModuleCat R R}
    (g : N.asBilinForm.IsometryEquiv N.asBilinForm) :
    toMathlibIsometryEquiv (fromMathlibIsometryEquiv g) = g :=
  rfl

/-- Regard an orthogonal-group element as an automorphism in the formed-module category. -/
def toIso (g : OrthogonalGroup M) : M ≅ M where
  hom := BilinModuleCat.homMk g.1.toLinearMap g.property
  inv := BilinModuleCat.homMk g.1.symm.toLinearMap (fun x y ↦ by
    simpa using (g.property (g.1.symm x) (g.1.symm y)).symm)
  hom_inv_id := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    exact g.1.symm_apply_apply x
  inv_hom_id := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    exact g.1.apply_symm_apply x

@[simp]
theorem underlyingMap_toIso_hom (g : OrthogonalGroup M) :
    BilinModuleCat.underlyingMap (toIso g).hom = g.1.toLinearMap :=
  rfl

/-- The action of the orthogonal group on the carrier. -/
def actOnVector (g : OrthogonalGroup M) (x : M.carrier) : M.carrier :=
  g.1 x

/-- The image of a submodule under an orthogonal-group element. -/
def actOnSubmodule (g : OrthogonalGroup M)
    (P : Submodule R M.carrier) : Submodule R M.carrier :=
  P.map g.1.toLinearMap

@[simp]
theorem actOnSubmodule_one (P : Submodule R M.carrier) :
    actOnSubmodule (1 : OrthogonalGroup M) P = P := by
  simp [actOnSubmodule]

theorem actOnSubmodule_mul (g h : OrthogonalGroup M)
    (P : Submodule R M.carrier) :
    actOnSubmodule (g * h) P =
      actOnSubmodule g (actOnSubmodule h P) := by
  exact Submodule.map_comp h.1.toLinearMap g.1.toLinearMap P

/-- The orthogonal group acts on submodules by linear image. -/
instance submoduleMulAction (M : BilinModuleCat R W) :
    MulAction (OrthogonalGroup M) (Submodule R M.carrier) where
  smul := actOnSubmodule
  one_smul := actOnSubmodule_one
  mul_smul := actOnSubmodule_mul

@[simp]
theorem smul_submodule_eq_actOnSubmodule (g : OrthogonalGroup M)
    (P : Submodule R M.carrier) :
    g • P = actOnSubmodule g P :=
  rfl

end OrthogonalGroup

end BilinModuleCat

end LeanCategories.Modules.Bilinear.Valued
