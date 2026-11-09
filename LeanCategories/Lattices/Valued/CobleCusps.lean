/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CobleLattice

/-!
# The cusps of the Coble lattice (#115)

`T_Co` has a primitive isotropic vector: the second standard basis vector — the first generator of
the first hyperbolic block — spans a totally isotropic primitive line, since its square is zero and
its coordinates are `0` away from its own index. The line gives the 0-cusps.

With that vector in hand the two descent statements of #113 are instantiated at `T_Co`:

* the quadratic fibre theorem `vectorFibreEquivQuadraticSurjective` at the Coble vector, with the
  discriminant class and the stabilizer fixation as named hypotheses, and
* the double-coset description `cuspOrbitsEquivDoubleCosetsDiscriminant` at a primitive isotropic
  plane, with the plane and the containment of the stable group as named hypotheses.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

-- The quotient module instance of the discriminant carrier, pinned as in `CobleLattice`.
attribute [local instance 10000] Submodule.Quotient.module

/-! ## Coordinates of standard basis vectors -/

/-- A standard basis vector vanishes away from its own index. -/
theorem basisFun_apply_of_ne {i j : Fin 13} (h : j ≠ i) :
    (Pi.basisFun ℤ (Fin 13)) i j = 0 := by
  simp only [Pi.basisFun_apply]
  exact Pi.single_eq_of_ne (M := fun _ => ℤ) h 1

/-- A standard basis vector takes the value one at its own index. -/
theorem basisFun_apply_self (i : Fin 13) : (Pi.basisFun ℤ (Fin 13)) i i = 1 := by
  simp only [Pi.basisFun_apply]
  exact Pi.single_eq_same i 1

/-- The first generator of the first hyperbolic block: the Coble vector. -/
noncomputable def cobleVectorCoord : Fin 13 → ℤ := (Pi.basisFun ℤ (Fin 13)) 1

/-! ## The primitive isotropic vector -/

/-- The square of the Coble vector vanishes. -/
theorem cobleVectorCoord_isotropic :
    cobleLattice.obj.pairing cobleVectorCoord cobleVectorCoord = 0 := by
  have h := coble_pairing_basis (1 : Fin 13) (1 : Fin 13)
  have hz : cobleGramMatrix (1 : Fin 13) (1 : Fin 13) = 0 := by decide
  simpa only [cobleVectorCoord, hz] using h

/-- The Coble vector is indivisible: one of its coordinates is a unit. -/
theorem cobleVectorCoord_indivisible (c : ℤ) (w : Fin 13 → ℤ)
    (h : cobleVectorCoord = c • w) : IsUnit c := by
  have h1 := congrFun h 1
  rw [cobleVectorCoord, basisFun_apply_self, Pi.smul_apply, smul_eq_mul] at h1
  exact IsUnit.of_mul_eq_one (w 1) h1.symm

/-- The line spanned by the Coble vector is primitive. -/
theorem cobleVectorCoord_primitiveSpan :
    IsPrimitiveSubmodule (Submodule.span ℤ {cobleVectorCoord}) := by
  rw [isPrimitiveSubmodule_iff_saturation_eq]
  refine le_antisymm ?_ (le_saturation _)
  intro x hx
  obtain ⟨a, ha, hax⟩ := (mem_saturation_iff (R := ℤ) _ x).mp hx
  rw [Submodule.mem_span_singleton] at hax ⊢
  obtain ⟨k, hk⟩ := hax
  refine ⟨x 1, ?_⟩
  funext j
  by_cases hj : j = 1
  · subst hj
    rw [Pi.smul_apply, smul_eq_mul, cobleVectorCoord, basisFun_apply_self, mul_one]
  · have hzero : a * x j = 0 := by
      have hj1 : (cobleVectorCoord : Fin 13 → ℤ) j = 0 := by
        rw [cobleVectorCoord]
        exact basisFun_apply_of_ne hj
      have h := congrFun hk j
      simp only [Pi.smul_apply, smul_eq_mul, hj1, mul_zero] at h
      exact h.symm
    simp only [cobleVectorCoord, Pi.smul_apply, smul_eq_mul, basisFun_apply_of_ne hj,
      mul_zero]
    exact ((mul_eq_zero.mp hzero).resolve_left ha).symm

/-- The Coble vector as a primitive isotropic vector of `T_Co`. -/
noncomputable def cobleVector : PrimitiveIsotropicVector cobleLattice where
  toVector := cobleVectorCoord
  nonzero := by
    intro hzero
    have h1 := congrFun hzero 1
    rw [cobleVectorCoord, basisFun_apply_self] at h1
    exact one_ne_zero h1
  isotropic := cobleVectorCoord_isotropic
  indivisible := cobleVectorCoord_indivisible
  primitiveSpan := cobleVectorCoord_primitiveSpan

/-- The primitive isotropic line of the Coble vector: a 0-cusp of `F_Co`. -/
noncomputable def cobleLine : PrimitiveIsotropic cobleLattice 1 :=
  @PrimitiveIsotropicVector.toLine ℤ _ _ cobleLattice cobleLatticeCarrierTorsionFree cobleVector

/-! ## The cusp sets are inhabited -/

/-- The `ker ρ`-orbit set of primitive isotropic lines is inhabited. -/
theorem cobleCuspOrbitsKernelOne_nonempty : Nonempty cobleCuspOrbitsKernelOne :=
  ⟨CuspOrbits.mk cobleKernelSubgroup cobleLine⟩

/-- The `Γ_Co`-orbit set of primitive isotropic lines is inhabited. -/
theorem cobleCuspOrbitsGammaOne_nonempty : Nonempty cobleCuspOrbitsGammaOne :=
  ⟨CuspOrbits.mk cobleGammaCoSubgroup cobleLine⟩

/-! ## The quadratic fibre theorem at the Coble vector -/

set_option maxHeartbeats 1200000 in
-- instantiating the theorem re-elaborates the nested `DoubleCoset.Quotient` type, as in the
-- worked instance of #113
/-- **The `T_Co` instance of the quadratic-discriminant fibre theorem** (#113, #115): for a class
`c` of the quadratic discriminant module fixed by the stabilizer of the Coble vector (`hstab`) and
a surjective discriminant representation (`hσ`), the fibre of the class map
`ker ρ · g · Stab(v) ↦ ρ(g)·c` over `c` is `Stab_{O(q)}(c)` modulo `ρ(Stab_{O(T_Co)}(v))`.

The two hypotheses are named: the class `c` is not derived from `v`, and surjectivity of `ρ` onto
`O(q_{T_Co})` is *not* proved here — for a `2`-elementary discriminant form the image of `O(T_Co)`
need not be the whole orthogonal group. Both are the hypotheses the issue of #115 allows to be
named. -/
noncomputable def cobleQuadraticFibre
    (c : cobleQuadraticDiscriminant.carrier)
    (hstab : ∀ s : OrthogonalGroup cobleLattice,
      s ∈ MulAction.stabilizer (OrthogonalGroup cobleLattice) cobleVector → cobleRho s • c = c)
    (hσ : Function.Surjective cobleRho) :=
  @vectorFibreEquivQuadraticSurjective ℤ _ _ cobleLattice cobleLatticeCarrierTorsionFree
    coble_isFractionFieldPerfect coble_isEven cobleVector c hstab hσ

/-! ## The double-coset description at a Coble plane -/

/-- The `T_Co` instance of `cuspOrbitsEquivDoubleCosetsDiscriminant` (#115) for a primitive
isotropic **plane** `N`: the `ker ρ`-orbits of planes lying over the `O(T_Co)`-orbit of `N` are the
double cosets of `ρ(ker ρ)` and `ρ(Stab(N))` in the discriminant range.

The plane `N` and the containment `ker ρ_bilin ≤ ker ρ` are named hypotheses. The containment is
the hypothesis of the descent theorem; it is *not* an artefact here: `q_{T_Co}` determines the
bilinear form, so the quadratic kernel is contained in the bilinear one, and the two agree only on
the part of the discriminant form that sees `q`. -/
noncomputable def cobleCuspOrbitsEquivDoubleCosetsPlane
    (hKΓ : OrthogonalGroup.stableOrthogonalGroup coble_isFractionFieldPerfect ≤
      cobleKernelSubgroup.toSubgroup)
    (N : PrimitiveIsotropic cobleLattice 2) :=
  cuspOrbitsEquivDoubleCosetsDiscriminant coble_isFractionFieldPerfect cobleKernelSubgroup hKΓ N

end LeanCategories.Lattices.Valued
