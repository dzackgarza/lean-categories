/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ComplexTorus
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Complex structures and Riemann forms

`LeanCategories.Lattices.Valued.ComplexTorus` builds the real torus `L_ℝ / L` of a realized
integral lattice and stops there, because a real torus is not yet a complex torus. This file
supplies the two missing pieces of data named in that file.

## Complex structure

A complex structure on a real vector space `E` is an `ℝ`-linear `J : E → E` with `J ∘ J = -1`.
Such a `J` is exactly the same thing as an `ℝ`-algebra map `ℂ → End_ℝ(E)`, because
`ℂ = ℝ[X] / (X² + 1)`. Mathlib packages that universal property as `Complex.liftAux`, so the
induced `Module ℂ E` needs no hand-rolled scalar action: it is `Module.compHom` along the
algebra map, using `Module.End.applyModule` for the tautological action of `End_ℝ(E)` on `E`.

## Riemann form

A Riemann form is an alternating `ℝ`-bilinear form `b` on `E` that is `J`-invariant and satisfies
`0 < b x (J x)` for `x ≠ 0`. This is the polarization condition: a complex torus `E / Λ` is an
abelian variety exactly when it carries a Riemann form whose restriction to `Λ` is integral. On
the lattice side, the integral form of an object of `FiniteProjectiveLatticeCat ℤ ℤ` induces a
candidate `b` by real scalar extension along a realization; whether that `b` is a Riemann form
depends on the chosen complex structure, so the two are kept separate here.

## Mathlib coverage

Mathlib has no `ComplexStructure`, no complex torus, no Riemann form and no abelian variety.
It does supply the algebraic heart of the `ℂ`-module structure through `Complex.liftAux`, so only
the packaging is built here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Lattices.Valued

universe u

/-- A complex structure on a real vector space: an `ℝ`-linear endomorphism squaring to `-1`. -/
structure ComplexStructure (E : Type u) [AddCommGroup E] [Module ℝ E] where
  /-- The endomorphism acting as multiplication by `i`. -/
  J : E →ₗ[ℝ] E
  /-- `J` squares to minus the identity. -/
  sq : J.comp J = -LinearMap.id

namespace ComplexStructure

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- `J` squares to `-1` in the endomorphism ring, the form `Complex.liftAux` expects. -/
theorem mul_self (Jstr : ComplexStructure E) :
    (Jstr.J : Module.End ℝ E) * Jstr.J = -1 :=
  Jstr.sq

/-- The `ℝ`-algebra map `ℂ → End_ℝ(E)` determined by a complex structure, obtained from the
presentation `ℂ = ℝ[X] / (X² + 1)` through `Complex.liftAux`. -/
def algHom (Jstr : ComplexStructure E) : ℂ →ₐ[ℝ] Module.End ℝ E :=
  Complex.liftAux (Jstr.J : Module.End ℝ E) Jstr.mul_self

/-- The algebra map sends `i` to `J`. -/
@[simp]
theorem algHom_I (Jstr : ComplexStructure E) : Jstr.algHom Complex.I = Jstr.J :=
  Complex.liftAux_apply_I _ _

/-- The `ℂ`-module structure induced by a complex structure, restricting to the given real
scalar action. -/
@[reducible]
def module (Jstr : ComplexStructure E) : Module ℂ E :=
  Module.compHom E (Jstr.algHom : ℂ →+* Module.End ℝ E)

/-- The induced complex action is `(a + b i) • x = a • x + b • J x`. -/
theorem module_smul (Jstr : ComplexStructure E) (z : ℂ) (x : E) :
    letI := Jstr.module
    z • x = z.re • x + z.im • Jstr.J x := by
  change Jstr.algHom z x = _
  simp [algHom, Complex.liftAux_apply]

/-- The induced complex action restricts along `ℝ → ℂ` to the original real action. -/
theorem module_real_smul (Jstr : ComplexStructure E) (r : ℝ) (x : E) :
    letI := Jstr.module
    (r : ℂ) • x = r • x := by
  rw [Jstr.module_smul]
  simp

/-- A bilinear form is compatible with a complex structure when `J` is an isometry for it. -/
def IsCompatible (b : LinearMap.BilinForm ℝ E) (Jstr : ComplexStructure E) : Prop :=
  ∀ x y, b (Jstr.J x) (Jstr.J y) = b x y

/-- A Riemann form for a complex structure `Jstr`: an alternating `J`-invariant bilinear form
whose associated hermitian pairing is positive definite.

This is the polarization condition. A complex torus `E / Λ` is an abelian variety exactly when
some Riemann form on `E` restricts to an integral form on `Λ`; without such a form the torus
carries no ample line bundle and is not projective. The integral bilinear form of a lattice in
`FiniteProjectiveLatticeCat ℤ ℤ` induces a real form on a realization by scalar extension, and
that real form is a Riemann form precisely when it satisfies the three conditions below for the
chosen complex structure. -/
structure IsRiemannForm (b : LinearMap.BilinForm ℝ E) (Jstr : ComplexStructure E) : Prop where
  /-- The form is alternating. -/
  alt : b.IsAlt
  /-- `J` preserves the form. -/
  compat : IsCompatible b Jstr
  /-- The associated symmetric form `(x, y) ↦ b x (J y)` is positive definite. -/
  pos : ∀ x : E, x ≠ 0 → 0 < b x (Jstr.J x)

/-- A Riemann form is skew-symmetric. -/
theorem IsRiemannForm.neg_swap {b : LinearMap.BilinForm ℝ E} {Jstr : ComplexStructure E}
    (h : IsRiemannForm b Jstr) (x y : E) : b y x = -b x y :=
  (h.alt.neg_eq x y).symm

/-- A Riemann form vanishes only at zero in the positivity direction. -/
theorem IsRiemannForm.ne_zero_of_pos {b : LinearMap.BilinForm ℝ E} {Jstr : ComplexStructure E}
    (h : IsRiemannForm b Jstr) {x : E} (hx : x ≠ 0) : b x (Jstr.J x) ≠ 0 :=
  ne_of_gt (h.pos x hx)

end ComplexStructure

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace FiniteProjectiveLatticeCat

/-- A complex structure preserving a realized lattice descends to its real torus. The hypothesis
is exactly the stability of the realized lattice under `J`; it is what makes `L_ℝ / L` a complex
torus rather than only a real one. -/
def realQuotientJ (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E)
    (Jstr : ComplexStructure E)
    (h : L.realLatticeImage b c ≤ (L.realLatticeImage b c).comap (Jstr.J.restrictScalars ℤ)) :
    L.realQuotient b c →ₗ[ℤ] L.realQuotient b c :=
  Submodule.mapQ _ _ (Jstr.J.restrictScalars ℤ) h

/-- The descended endomorphism commutes with the quotient map. -/
@[simp]
theorem realQuotientJ_mk (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E)
    (Jstr : ComplexStructure E)
    (h : L.realLatticeImage b c ≤ (L.realLatticeImage b c).comap (Jstr.J.restrictScalars ℤ))
    (x : E) :
    L.realQuotientJ b c Jstr h (L.realQuotientMk b c x) = L.realQuotientMk b c (Jstr.J x) :=
  rfl

/-- The descended endomorphism still squares to `-1`, so the real torus of a `J`-stable lattice
is a complex torus. -/
theorem realQuotientJ_sq (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E)
    (Jstr : ComplexStructure E)
    (h : L.realLatticeImage b c ≤ (L.realLatticeImage b c).comap (Jstr.J.restrictScalars ℤ))
    (y : L.realQuotient b c) :
    L.realQuotientJ b c Jstr h (L.realQuotientJ b c Jstr h y) = -y := by
  refine Quotient.inductionOn' y fun x => ?_
  have hx : Jstr.J (Jstr.J x) = -x := congrFun (congrArg DFunLike.coe Jstr.sq) x
  change Submodule.Quotient.mk (Jstr.J (Jstr.J x)) = -Submodule.Quotient.mk x
  rw [hx, Submodule.Quotient.mk_neg]

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
