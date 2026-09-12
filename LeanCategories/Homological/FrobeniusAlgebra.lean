/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.IsQuasiFrobenius
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Frobenius algebras

Weibel, *An Introduction to Homological Algebra*, Definition 4.2.5 (FC05-C04-U019).

A finite-dimensional algebra `R` over a field `k` is Frobenius when the right regular
`R`-module is isomorphic to its `k`-linear dual.  We record the right-module compatibility
explicitly on a `k`-linear equivalence; this avoids installing an orphan right-`R` module
instance on `Module.Dual k R`.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable (k : Type u) (R : Type v) [Field k] [Ring R] [Algebra k R]

/-- A source-faithful self-duality datum for a Frobenius algebra.

The equation says that the linear equivalence is right `R`-linear for the standard right
action on the dual, `(f · r)(x) = f (r * x)`. -/
structure FrobeniusSelfDuality where
  equiv : R ≃ₗ[k] Module.Dual k R
  map_mul_apply : ∀ a r x : R, equiv (a * r) x = equiv a (r * x)

/-- A finite-dimensional `k`-algebra is Frobenius when its right regular module is isomorphic
to its `k`-linear dual (Weibel, Definition 4.2.5). -/
def IsFrobeniusAlgebra : Prop :=
  FiniteDimensional k R ∧ Nonempty (FrobeniusSelfDuality k R)

namespace FrobeniusDual

/-- The `k`-dual, regarded as a right `R`-module by precomposition with left multiplication. -/
def Right := Module.Dual k R

instance rightAddCommGroup : AddCommGroup (Right k R) := by
  dsimp [Right]
  infer_instance

instance rightSMul : SMul Rᵐᵒᵖ (Right k R) where
  smul r f :=
    show Module.Dual k R from
      { toFun := fun x => (show Module.Dual k R from f) (r.unop * x)
        map_add' := by
          intro x y
          rw [mul_add, (show Module.Dual k R from f).map_add]
        map_smul' := by
          intro c x
          rw [Algebra.mul_smul_comm]
          exact (show Module.Dual k R from f).map_smul c (r.unop * x) }

@[simp] theorem right_smul_apply (r : Rᵐᵒᵖ) (f : Right k R) (x : R) :
    (show Module.Dual k R from r • f) x =
      (show Module.Dual k R from f) (r.unop * x) := rfl

@[ext] theorem Right.ext {f g : Right k R}
    (h : ∀ x : R, (show Module.Dual k R from f) x = (show Module.Dual k R from g) x) :
    f = g := by
  change (show Module.Dual k R from f) = (show Module.Dual k R from g)
  ext x
  exact h x

@[simp] theorem Right.add_apply (f g : Right k R) (x : R) :
    (show Module.Dual k R from f + g) x =
      (show Module.Dual k R from f) x + (show Module.Dual k R from g) x := rfl

@[simp] theorem Right.map_add (f : Right k R) (x y : R) :
    (show Module.Dual k R from f) (x + y) =
      (show Module.Dual k R from f) x + (show Module.Dual k R from f) y :=
  (show Module.Dual k R from f).map_add x y

instance rightModule : Module Rᵐᵒᵖ (Right k R) :=
  Module.ofMinimalAxioms
    (fun r f g => by
      ext x
      change
        (show Module.Dual k R from f) (r.unop * x) +
            (show Module.Dual k R from g) (r.unop * x) =
          (show Module.Dual k R from f) (r.unop * x) +
            (show Module.Dual k R from g) (r.unop * x)
      rfl)
    (fun r s f => by
      ext x
      simp [add_mul])
    (fun r s f => by ext x; simp [mul_assoc])
    (fun f => by ext x; simp)

/-- The `k`-dual, regarded as a left `R`-module by precomposition with right multiplication. -/
def Left := Module.Dual k R

instance leftAddCommGroup : AddCommGroup (Left k R) := by
  dsimp [Left]
  infer_instance

instance leftSMul : SMul R (Left k R) where
  smul r f :=
    show Module.Dual k R from
      { toFun := fun x => (show Module.Dual k R from f) (x * r)
        map_add' := by
          intro x y
          rw [add_mul, (show Module.Dual k R from f).map_add]
        map_smul' := by
          intro c x
          rw [Algebra.smul_mul_assoc]
          exact (show Module.Dual k R from f).map_smul c (x * r) }

@[simp] theorem left_smul_apply (r : R) (f : Left k R) (x : R) :
    (show Module.Dual k R from r • f) x =
      (show Module.Dual k R from f) (x * r) := rfl

@[ext] theorem Left.ext {f g : Left k R}
    (h : ∀ x : R, (show Module.Dual k R from f) x = (show Module.Dual k R from g) x) :
    f = g := by
  change (show Module.Dual k R from f) = (show Module.Dual k R from g)
  ext x
  exact h x

@[simp] theorem Left.add_apply (f g : Left k R) (x : R) :
    (show Module.Dual k R from f + g) x =
      (show Module.Dual k R from f) x + (show Module.Dual k R from g) x := rfl

@[simp] theorem Left.map_add (f : Left k R) (x y : R) :
    (show Module.Dual k R from f) (x + y) =
      (show Module.Dual k R from f) x + (show Module.Dual k R from f) y :=
  (show Module.Dual k R from f).map_add x y

instance leftModule : Module R (Left k R) :=
  Module.ofMinimalAxioms
    (fun r f g => by
      ext x
      change
        (show Module.Dual k R from f) (x * r) +
            (show Module.Dual k R from g) (x * r) =
          (show Module.Dual k R from f) (x * r) +
            (show Module.Dual k R from g) (x * r)
      rfl)
    (fun r s f => by
      ext x
      simp [mul_add])
    (fun r s f => by ext x; simp [mul_assoc])
    (fun f => by ext x; simp)

/-- The right `R`-module `Hom_k(R,k)` is injective. This is the standard coinduced-module
argument: a map from a right ideal is determined by its value at `1`, that `k`-linear
functional extends to all of `R`, and the extension is then recoinduced. -/
theorem right_injective : Module.Injective Rᵐᵒᵖ (Right k R) :=
  Module.Baer.injective fun I g => by
    let Iₖ : Submodule k Rᵐᵒᵖ := I.restrictScalars k
    let ellI : Iₖ →ₗ[k] k :=
      { toFun := fun x =>
          (show Module.Dual k R from g ⟨x.1, x.2⟩) 1
        map_add' := by
          intro x y
          change
            (show Module.Dual k R from g (⟨x.1, x.2⟩ + ⟨y.1, y.2⟩)) 1 = _
          rw [g.map_add]
          rfl
        map_smul' := by
          intro c x
          let xI : I := ⟨x.1, x.2⟩
          have hx : (⟨(c • x).1, (c • x).2⟩ : I) =
              (algebraMap k Rᵐᵒᵖ c) • xI := by
            apply Subtype.ext
            simp [Iₖ, xI, Algebra.smul_def]
          change
            (show Module.Dual k R from g ⟨(c • x).1, (c • x).2⟩) 1 =
              c • (show Module.Dual k R from g xI) 1
          rw [hx, g.map_smul, right_smul_apply]
          simpa [Algebra.smul_def] using
            (show Module.Dual k R from g xI).map_smul c (1 : R) }
    obtain ⟨ell, hell⟩ := LinearMap.exists_extend ellI
    let lambda : Right k R :=
      show Module.Dual k R from
        ell.comp (MulOpposite.opLinearEquiv k).toLinearMap
    refine ⟨
      { toFun := fun r => r • lambda
        map_add' := fun r s => add_smul r s lambda
        map_smul' := fun r s => mul_smul r s lambda }, ?_⟩
    intro x hx
    ext a
    let hmem : MulOpposite.op a * x ∈ I := I.mul_mem_left _ hx
    let z : Iₖ := ⟨MulOpposite.op a * x, hmem⟩
    have hext := DFunLike.congr_fun hell z
    have hg := congrArg
      (fun f : Right k R => (show Module.Dual k R from f) 1)
      (g.map_smul (MulOpposite.op a) ⟨x, hx⟩)
    change ell (MulOpposite.op (x.unop * a)) =
      (show Module.Dual k R from g ⟨x, hx⟩) a
    rw [MulOpposite.op_mul]
    calc
      ell (MulOpposite.op a * x) = ellI z := by simpa [Iₖ, z] using hext
      _ = (show Module.Dual k R from g ⟨MulOpposite.op a * x, hmem⟩) 1 := rfl
      _ = (show Module.Dual k R from g ⟨x, hx⟩) a := by
        simpa [hmem] using hg

/-- The left `R`-module `Hom_k(R,k)` is injective. -/
theorem left_injective : Module.Injective R (Left k R) :=
  Module.Baer.injective fun I g => by
    let Iₖ : Submodule k R := I.restrictScalars k
    let ellI : Iₖ →ₗ[k] k :=
      { toFun := fun x =>
          (show Module.Dual k R from g ⟨x.1, x.2⟩) 1
        map_add' := by
          intro x y
          change
            (show Module.Dual k R from g (⟨x.1, x.2⟩ + ⟨y.1, y.2⟩)) 1 = _
          rw [g.map_add]
          rfl
        map_smul' := by
          intro c x
          let xI : I := ⟨x.1, x.2⟩
          have hx : (⟨(c • x).1, (c • x).2⟩ : I) =
              (algebraMap k R c) • xI := by
            apply Subtype.ext
            simp [Iₖ, xI, Algebra.smul_def]
          change
            (show Module.Dual k R from g ⟨(c • x).1, (c • x).2⟩) 1 =
              c • (show Module.Dual k R from g xI) 1
          rw [hx, g.map_smul, left_smul_apply]
          simpa [Algebra.smul_def] using
            (show Module.Dual k R from g xI).map_smul c (1 : R) }
    obtain ⟨ell, hell⟩ := LinearMap.exists_extend ellI
    let lambda : Left k R := show Module.Dual k R from ell
    refine ⟨
      { toFun := fun r => r • lambda
        map_add' := fun r s => add_smul r s lambda
        map_smul' := fun r s => mul_smul r s lambda }, ?_⟩
    intro x hx
    ext a
    let hmem : a * x ∈ I := I.mul_mem_left _ hx
    let z : Iₖ := ⟨a * x, hmem⟩
    have hext := DFunLike.congr_fun hell z
    have hg := congrArg
      (fun f : Left k R => (show Module.Dual k R from f) 1)
      (g.map_smul a ⟨x, hx⟩)
    change ell (a * x) = (show Module.Dual k R from g ⟨x, hx⟩) a
    calc
      ell (a * x) = ellI z := by simpa [Iₖ, z] using hext
      _ = (show Module.Dual k R from g ⟨a * x, hmem⟩) 1 := rfl
      _ = (show Module.Dual k R from g ⟨x, hx⟩) a := by
        simpa [hmem] using hg

end FrobeniusDual

namespace FrobeniusSelfDuality

variable {k R}

/-- The source right-module self-duality, expressed as an actual `Rᵐᵒᵖ`-linear equivalence. -/
def rightModuleEquiv (e : FrobeniusSelfDuality k R) :
    R ≃ₗ[Rᵐᵒᵖ] FrobeniusDual.Right k R where
  toFun a := e.equiv a
  invFun f := e.equiv.symm (show Module.Dual k R from f)
  left_inv a := e.equiv.symm_apply_apply a
  right_inv f := by
    change e.equiv (e.equiv.symm (show Module.Dual k R from f)) =
      (show Module.Dual k R from f)
    exact e.equiv.apply_symm_apply _
  map_add' a b := e.equiv.map_add a b
  map_smul' r a := by
    apply FrobeniusDual.Right.ext
    intro x
    change e.equiv (a * r.unop) x = e.equiv a (r.unop * x)
    exact e.map_mul_apply a r.unop x

/-- The transpose of a Frobenius right self-duality. Its value at `a` is the functional
`x ↦ e(x)(a)`. -/
def leftMap (e : FrobeniusSelfDuality k R) : R →ₗ[k] Module.Dual k R where
  toFun a :=
    { toFun := fun x => e.equiv x a
      map_add' := fun x y => by rw [e.equiv.map_add]; rfl
      map_smul' := fun c x => by rw [e.equiv.map_smul]; rfl }
  map_add' a b := by
    ext x
    exact (e.equiv x).map_add a b
  map_smul' c a := by
    ext x
    exact (e.equiv x).map_smul c a

theorem leftMap_injective (e : FrobeniusSelfDuality k R) : Function.Injective e.leftMap := by
  intro a b hab
  have hzero : e.leftMap (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hall : ∀ phi : Module.Dual k R, phi (a - b) = 0 := by
    intro phi
    obtain ⟨x, rfl⟩ := e.equiv.surjective phi
    exact DFunLike.congr_fun hzero x
  have hsub : a - b = 0 := (Module.forall_dual_apply_eq_zero_iff k (a - b)).mp hall
  exact sub_eq_zero.mp hsub

/-- Finite-dimensionality turns the transpose of the right self-duality into a linear
equivalence. -/
noncomputable def leftLinearEquiv (e : FrobeniusSelfDuality k R) [FiniteDimensional k R] :
    R ≃ₗ[k] Module.Dual k R :=
  e.leftMap.linearEquivOfInjective e.leftMap_injective
    (Subspace.dual_finrank_eq (K := k) (V := R)).symm

/-- A Frobenius right self-duality induces the corresponding left-module self-duality. -/
noncomputable def leftModuleEquiv (e : FrobeniusSelfDuality k R) [FiniteDimensional k R] :
    R ≃ₗ[R] FrobeniusDual.Left k R where
  toFun a := e.leftLinearEquiv a
  invFun f := e.leftLinearEquiv.symm (show Module.Dual k R from f)
  left_inv a := e.leftLinearEquiv.symm_apply_apply a
  right_inv f := by
    change e.leftLinearEquiv (e.leftLinearEquiv.symm (show Module.Dual k R from f)) =
      (show Module.Dual k R from f)
    exact e.leftLinearEquiv.apply_symm_apply _
  map_add' a b := e.leftLinearEquiv.map_add a b
  map_smul' r a := by
    apply FrobeniusDual.Left.ext
    intro x
    change e.equiv x (r * a) = e.equiv (x * r) a
    exact (e.map_mul_apply x r a).symm

end FrobeniusSelfDuality

universe uS uM uN

private theorem injective_of_linearEquiv
    {S : Type uS} [Ring S] {M : Type uM} {N : Type uN}
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    [Small.{uN} S]
    (e : M ≃ₗ[S] N) (hN : Module.Injective S N) : Module.Injective S M :=
  Module.Baer.injective
    ((Module.Baer.congr e.symm).mp (Module.Baer.of_injective hN))

namespace IsFrobeniusAlgebra

variable {k R}

/-- Every Frobenius algebra is quasi-Frobenius (Weibel, after Definition 4.2.5). -/
theorem isQuasiFrobenius (h : IsFrobeniusAlgebra k R) : IsQuasiFrobenius R := by
  rcases h with ⟨hfin, ⟨e⟩⟩
  let _ : FiniteDimensional k R := hfin
  let _ : FiniteDimensional k Rᵐᵒᵖ :=
    FiniteDimensional.of_surjective (MulOpposite.opLinearEquiv k).toLinearMap
      (MulOpposite.opLinearEquiv k).surjective
  let _ : IsNoetherianRing R := IsNoetherianRing.of_finite k R
  let _ : IsNoetherianRing Rᵐᵒᵖ := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  have hleft : Module.Injective R R :=
    injective_of_linearEquiv e.leftModuleEquiv (FrobeniusDual.left_injective k R)
  have hright : Module.Injective Rᵐᵒᵖ R :=
    injective_of_linearEquiv e.rightModuleEquiv (FrobeniusDual.right_injective k R)
  exact ⟨inferInstance, inferInstance, hleft, hright⟩

end IsFrobeniusAlgebra

end LeanCategories.Homological
