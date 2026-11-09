/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CobleLattice

/-!
# The cusps of the Coble lattice (#115)

`T_Co = ⟨2⟩ ⊕ U(2) ⊕ E₈(−2)` has signature `(2, 9)`, so primitive isotropic lines and primitive
isotropic planes both exist and the rank-1 and rank-2 orbit sets are inhabited.

* The primitive isotropic vector is `v = e₁`, the first generator of `U(2)`: `(v, v) = 0` and `v` is
  indivisible.
* The primitive isotropic plane is spanned by `v` and by `w = 2e₀ + e₃ + e₄`, where `e₀` generates
  `⟨2⟩` and `e₃, e₄` are two `E₈(−2)` coordinates with `(e₃, e₄) = 0`: then
  `(w, w) = 4 + (−2) + (−2) = 0` and `(v, w) = 0`. Its primitivity is the coordinate functional
  `e₃^*`, which is `1` on `w` and `0` on `v`, so a multiple of a vector of the plane is a multiple
  of `v` with an integral coefficient.

The generators are explicit integer vectors, so their pairings are decided by reduction on the Gram
matrix; arbitrary vectors of the packaged carrier are read through `cobleCoordEquiv`, the linear
equivalence between the carrier and `Fin 11 → ℤ`.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

-- The quotient module instance of the discriminant carrier, pinned as in `CobleLattice`.
attribute [local instance 10000] Submodule.Quotient.module

/-! ## Coordinates -/

/-- The coordinate equivalence is the identity on vectors of the carrier. -/
theorem cobleCoordEquiv_apply (x : ↥cobleLattice.obj.carrier) :
    cobleCoordEquiv x = (x : Fin 11 → ℤ) := by
  rw [cobleCoordEquiv, Pi.basisFun_equivFun]
  rfl

/-- The coordinate equivalence is the identity on coordinate vectors. -/
theorem cobleCoordEquiv_coe (x : Fin 11 → ℤ) :
    cobleCoordEquiv (x : ↥cobleLattice.obj.carrier) = x :=
  cobleCoordEquiv_apply _

/-- The `i`-th coordinate functional of `T_Co`. -/
noncomputable def cobleCoordFun (i : Fin 11) : ↥cobleLattice.obj.carrier →ₗ[ℤ] ℤ :=
  (LinearMap.proj i).comp cobleCoordEquiv.toLinearMap

theorem cobleCoordFun_apply (i : Fin 11) (x : ↥cobleLattice.obj.carrier) :
    cobleCoordFun i x = (x : Fin 11 → ℤ) i := by
  rw [cobleCoordFun, LinearMap.comp_apply, LinearMap.proj_apply]
  exact congrFun (cobleCoordEquiv_apply x) i

/-- The coordinate formula for the pairing of two vectors given by coordinates. -/
theorem coble_pairing_coord (x y : Fin 11 → ℤ) :
    cobleLattice.obj.pairing (x : ↥cobleLattice.obj.carrier) (y : ↥cobleLattice.obj.carrier)
      = ∑ i, ∑ j, x i * cobleGramMatrix i j * y j := by
  have h : cobleLattice.obj.pairing (x : ↥cobleLattice.obj.carrier)
      (y : ↥cobleLattice.obj.carrier) = Matrix.toBilin' cobleGramMatrix x y := rfl
  rw [h, Matrix.toBilin'_apply]

/-! ## The primitive isotropic vector -/

/-- The first generator of the first hyperbolic block, as an integer vector. -/
noncomputable def cobleVectorCoord : Fin 11 → ℤ := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The Coble vector has coordinate `1` at `1` and `0` elsewhere. -/
theorem cobleVectorCoord_apply (j : Fin 11) :
    cobleVectorCoord j = if j = 1 then 1 else 0 := by
  fin_cases j <;> simp [cobleVectorCoord]

/-- The square of the Coble vector vanishes. -/
theorem cobleVectorCoord_isotropic :
    cobleLattice.obj.pairing (cobleVectorCoord : ↥cobleLattice.obj.carrier)
      (cobleVectorCoord : ↥cobleLattice.obj.carrier) = 0 := by
  rw [coble_pairing_coord]
  decide

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
    rw [Pi.smul_apply, smul_eq_mul, cobleVectorCoord_apply, if_pos rfl, mul_one]
  · have hzero : a * x j = 0 := by
      have h := congrFun hk j
      simp only [Pi.smul_apply, smul_eq_mul, cobleVectorCoord_apply, if_neg hj,
        mul_zero] at h
      exact h.symm
    simp only [Pi.smul_apply, smul_eq_mul, cobleVectorCoord_apply, if_neg hj, mul_zero]
    exact ((mul_eq_zero.mp hzero).resolve_left ha).symm

/-- The Coble vector, as a vector of the packaged carrier. -/
noncomputable def coblePlaneV : ↥cobleLattice.obj.carrier := cobleVectorCoord

/-- The Coble line is primitive, as a submodule of the packaged carrier. -/
theorem coblePlaneV_primitiveSpan :
    IsPrimitiveSubmodule (Submodule.span ℤ {coblePlaneV}) :=
  cobleVectorCoord_primitiveSpan

/-- The first coordinate of the Coble vector. -/
theorem cobleCoordFun_planeV_one : cobleCoordFun 1 coblePlaneV = 1 := by
  rw [cobleCoordFun_apply, coblePlaneV]
  decide

/-- The third coordinate of the Coble vector. -/
theorem cobleCoordFun_planeV_three : cobleCoordFun 3 coblePlaneV = 0 := by
  rw [cobleCoordFun_apply, coblePlaneV]
  decide

/-- The Coble vector as a primitive isotropic vector of `T_Co`. -/
noncomputable def cobleVector : PrimitiveIsotropicVector cobleLattice where
  toVector := coblePlaneV
  nonzero := by
    intro hzero
    have h1 : cobleCoordFun 1 coblePlaneV = 1 := cobleCoordFun_planeV_one
    rw [hzero, map_zero] at h1
    exact one_ne_zero h1.symm
  isotropic := by
    simpa only [coblePlaneV] using cobleVectorCoord_isotropic
  indivisible := by
    intro c w hw
    have h := congrArg (cobleCoordFun 1) hw
    rw [map_smul, smul_eq_mul, cobleCoordFun_planeV_one] at h
    exact IsUnit.of_mul_eq_one (cobleCoordFun 1 w) h.symm
  primitiveSpan := coblePlaneV_primitiveSpan

/-- The primitive isotropic line of the Coble vector: a 0-cusp representative. -/
noncomputable def cobleLine : PrimitiveIsotropic cobleLattice 1 :=
  @PrimitiveIsotropicVector.toLine ℤ _ _ cobleLattice cobleLatticeCarrierTorsionFree cobleVector

/-! ## The primitive isotropic plane -/

/-- The vector `2e₀ + e₃ + e₄` of `⟨2⟩ ⊕ E₈(−2)`, as an integer vector. -/
noncomputable def coblePlaneWCoord : Fin 11 → ℤ := ![2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]

/-- `w` as a vector of the packaged carrier. -/
noncomputable def coblePlaneW : ↥cobleLattice.obj.carrier := coblePlaneWCoord

/-- The first coordinate of `w`. -/
theorem cobleCoordFun_planeW_one : cobleCoordFun 1 coblePlaneW = 0 := by
  rw [cobleCoordFun_apply, coblePlaneW]
  decide

/-- The third coordinate of `w`. -/
theorem cobleCoordFun_planeW_three : cobleCoordFun 3 coblePlaneW = 1 := by
  rw [cobleCoordFun_apply, coblePlaneW]
  decide

/-- The pairings between the two plane generators all vanish, computed from the Gram matrix. -/
theorem coblePlane_pairings :
    cobleLattice.obj.pairing coblePlaneV coblePlaneV = 0 ∧
    cobleLattice.obj.pairing coblePlaneV coblePlaneW = 0 ∧
    cobleLattice.obj.pairing coblePlaneW coblePlaneV = 0 ∧
    cobleLattice.obj.pairing coblePlaneW coblePlaneW = 0 := by
  have hv := coble_pairing_coord (x := cobleVectorCoord) (y := cobleVectorCoord)
  have hvw := coble_pairing_coord (x := cobleVectorCoord) (y := coblePlaneWCoord)
  have hwv := coble_pairing_coord (x := coblePlaneWCoord) (y := cobleVectorCoord)
  have hw := coble_pairing_coord (x := coblePlaneWCoord) (y := coblePlaneWCoord)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [coblePlaneV]
    rw [hv]
    decide
  · simp only [coblePlaneV, coblePlaneW]
    rw [hvw]
    decide
  · simp only [coblePlaneV, coblePlaneW]
    rw [hwv]
    decide
  · simp only [coblePlaneW]
    rw [hw]
    decide

/-- The span of two isotropic mutually orthogonal vectors is totally isotropic. -/
theorem isIsotropicSubmodule_span_pair (L : IntegralLatticeCat ℤ) (v w : L.obj.carrier)
    (hvv : L.obj.pairing v v = 0) (hvw : L.obj.pairing v w = 0)
    (hwv : L.obj.pairing w v = 0) (hww : L.obj.pairing w w = 0) :
    IsIsotropicSubmodule L (Submodule.span ℤ {v, w}) := by
  intro x hx y hy
  rw [IntegralLatticeCat.asBilinForm_apply]
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [BilinModuleCat.pairing_add_right, BilinModuleCat.pairing_add_left,
    BilinModuleCat.pairing_smul_right, BilinModuleCat.pairing_smul_left,
    hvv, hvw, hwv, hww, smul_zero, add_zero]

/-- The Coble plane is totally isotropic. -/
theorem coblePlane_isotropic :
    IsIsotropicSubmodule cobleLattice (Submodule.span ℤ {coblePlaneV, coblePlaneW}) :=
  isIsotropicSubmodule_span_pair cobleLattice coblePlaneV coblePlaneW
    coblePlane_pairings.1 coblePlane_pairings.2.1 coblePlane_pairings.2.2.1
    coblePlane_pairings.2.2.2

/-- A vector of the Coble plane is determined by its `1`-st and `3`-rd coordinates. -/
theorem coblePlane_decomp (z : ↥(Submodule.span ℤ {coblePlaneV, coblePlaneW})) :
    z.1 = (cobleCoordFun 1 z.1) • coblePlaneV + (cobleCoordFun 3 z.1) • coblePlaneW := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp z.2
  have ha : a = cobleCoordFun 1 z.1 := by
    rw [← hab]
    simp only [map_add, map_smul, smul_eq_mul, cobleCoordFun_planeV_one,
      cobleCoordFun_planeW_one, mul_zero, add_zero]
    ring
  have hb : b = cobleCoordFun 3 z.1 := by
    rw [← hab]
    simp only [map_add, map_smul, smul_eq_mul, cobleCoordFun_planeV_three,
      cobleCoordFun_planeW_three, mul_zero]
    ring
  rw [← ha, ← hb]
  exact hab.symm

/-- The plane's two coordinates, as a linear map. -/
noncomputable def coblePlaneCoord :
    ↥(Submodule.span ℤ {coblePlaneV, coblePlaneW}) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![cobleCoordFun 1 z.1, cobleCoordFun 3 z.1]
  map_add' z z' := by
    ext i
    fin_cases i <;> simp
  map_smul' c z := by
    ext i
    fin_cases i <;> simp

/-- The plane has rank two. -/
theorem coblePlane_finrank :
    Module.finrank ℤ ↥(Submodule.span ℤ {coblePlaneV, coblePlaneW}) = 2 := by
  have hinj : Function.Injective coblePlaneCoord := by
    intro z z' hzz'
    have h1 : cobleCoordFun 1 z.1 = cobleCoordFun 1 z'.1 := by
      have := congrFun hzz' 0
      simpa [coblePlaneCoord] using this
    have h3 : cobleCoordFun 3 z.1 = cobleCoordFun 3 z'.1 := by
      have := congrFun hzz' 1
      simpa [coblePlaneCoord] using this
    apply Subtype.ext
    rw [coblePlane_decomp z, coblePlane_decomp z', h1, h3]
  have hsurj : Function.Surjective coblePlaneCoord := by
    intro p
    refine ⟨⟨p 0 • coblePlaneV + p 1 • coblePlaneW, Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))⟩, ?_⟩
    funext i
    fin_cases i
    · change cobleCoordFun 1 (p 0 • coblePlaneV + p 1 • coblePlaneW) = p 0
      rw [map_add, map_smul, map_smul, cobleCoordFun_planeV_one, cobleCoordFun_planeW_one,
        smul_eq_mul, smul_eq_mul, mul_one, mul_zero, add_zero]
    · change cobleCoordFun 3 (p 0 • coblePlaneV + p 1 • coblePlaneW) = p 1
      rw [map_add, map_smul, map_smul, cobleCoordFun_planeV_three,
        cobleCoordFun_planeW_three, smul_eq_mul, smul_eq_mul, mul_zero, mul_one, zero_add]
  have e := LinearEquiv.ofBijective coblePlaneCoord ⟨hinj, hsurj⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The plane is primitive: the third coordinate functional is `1` on `w` and `0` on `v`, so the
coefficient of `w` in a multiple of a vector of the plane is that multiple times an integer. -/
theorem coblePlane_primitiveSpan :
    IsPrimitiveSubmodule (Submodule.span ℤ {coblePlaneV, coblePlaneW}) := by
  rw [isPrimitiveSubmodule_iff_saturation_eq]
  refine le_antisymm ?_ (le_saturation _)
  intro x hx
  obtain ⟨n, hn, hnx⟩ := (mem_saturation_iff (R := ℤ) _ x).mp hx
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hnx
  have hb : b = n * cobleCoordFun 3 x := by
    have h := congrArg (cobleCoordFun 3) hab
    simp only [map_add, map_smul, smul_eq_mul, cobleCoordFun_planeV_three,
      cobleCoordFun_planeW_three, mul_zero, mul_one, zero_add] at h
    exact h
  have hsplit : n • (x - (cobleCoordFun 3 x) • coblePlaneW)
      = n • x - (n * cobleCoordFun 3 x) • coblePlaneW := by
    rw [zsmul_sub, smul_smul]
  have hy : n • (x - (cobleCoordFun 3 x) • coblePlaneW) = a • coblePlaneV := by
    rw [hsplit, ← hb]
    exact sub_eq_iff_eq_add.mpr hab.symm
  have hyP : (x - (cobleCoordFun 3 x) • coblePlaneW) ∈ Submodule.span ℤ {coblePlaneV} := by
    rw [← (isPrimitiveSubmodule_iff_saturation_eq _).mp coblePlaneV_primitiveSpan]
    exact ⟨n, hn, hy ▸ Submodule.smul_mem _ _ (Submodule.subset_span (by simp))⟩
  have hx' : x = (x - (cobleCoordFun 3 x) • coblePlaneW) + (cobleCoordFun 3 x) • coblePlaneW := by
    abel
  rw [hx']
  exact Submodule.add_mem _ (Submodule.span_mono (by simp) hyP)
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The primitive isotropic plane of `T_Co`. -/
noncomputable def coblePlane : PrimitiveIsotropic cobleLattice 2 where
  toSubmodule := Submodule.span ℤ {coblePlaneV, coblePlaneW}
  isotropic := coblePlane_isotropic
  finrank_eq := coblePlane_finrank
  primitive := coblePlane_primitiveSpan

/-! ## The orbit sets are inhabited -/

/-- The `ker ρ`-orbit set of primitive isotropic lines is inhabited. -/
theorem cobleCuspOrbitsKernelOne_nonempty : Nonempty cobleCuspOrbitsKernelOne :=
  ⟨CuspOrbits.mk cobleKernelSubgroup cobleLine⟩

/-- The `ker ρ`-orbit set of primitive isotropic planes is inhabited. -/
theorem cobleCuspOrbitsKernelTwo_nonempty : Nonempty cobleCuspOrbitsKernelTwo :=
  ⟨CuspOrbits.mk cobleKernelSubgroup coblePlane⟩

/-- The `Γ_Co`-orbit set of primitive isotropic lines is inhabited. -/
theorem cobleCuspOrbitsGammaOne_nonempty (O : CobleOPlus) :
    Nonempty (cobleCuspOrbitsGammaOne O) :=
  ⟨CuspOrbits.mk (cobleGammaCoSubgroup O) cobleLine⟩

/-- The `Γ_Co`-orbit set of primitive isotropic planes is inhabited. -/
theorem cobleCuspOrbitsGammaTwo_nonempty (O : CobleOPlus) :
    Nonempty (cobleCuspOrbitsGammaTwo O) :=
  ⟨CuspOrbits.mk (cobleGammaCoSubgroup O) coblePlane⟩

/-! ## The two descent statements at `T_Co` -/

set_option maxHeartbeats 1200000 in
-- instantiating the theorem re-elaborates the nested `DoubleCoset.Quotient` type, as in the worked
-- instance of #113
/-- **The `T_Co` instance of the quadratic-discriminant fibre theorem** (#113, #115): for a class
`c` of the quadratic discriminant module fixed by the stabilizer of the Coble vector (`hstab`) and a
surjective quadratic discriminant representation (`hσ`), the fibre of the class map
`ker ρ · g · Stab(v) ↦ ρ(g)·c` over `c` is `Stab_{O(q)}(c)` modulo `ρ(Stab_{O(T_Co)}(v))`.

`hσ` is named. The proof stops at the computation of the image of
`OrthogonalGroup.evenDiscriminantRepresentation coble_isFractionFieldPerfect coble_isEven`: since
`T_Co = B(2)` with `B` odd unimodular, this is the image of `O(B)` in the orthogonal group of the
`2`-elementary form on `B / 2B`, and nothing in this development computes that image. Surjectivity
is not automatic — it is exactly what the `2`-adic discriminant form can obstruct. -/
noncomputable def cobleQuadraticFibre
    (c : cobleQuadraticDiscriminant.carrier)
    (hstab : ∀ s : OrthogonalGroup cobleLattice,
      s ∈ MulAction.stabilizer (OrthogonalGroup cobleLattice) cobleVector → cobleRho s • c = c)
    (hσ : Function.Surjective cobleRho) :=
  @vectorFibreEquivQuadraticSurjective ℤ _ _ cobleLattice cobleLatticeCarrierTorsionFree
    coble_isFractionFieldPerfect coble_isEven cobleVector c hstab hσ

/-- **The `T_Co` instance of the double-coset description of the cusps in an `O(T_Co)`-orbit**
(#113, #115), for a primitive isotropic **plane** `N`: the `ker ρ`-orbits of planes lying over the
`O(T_Co)`-orbit of `N` are the double cosets of `ρ(ker ρ)` and `ρ(Stab(N))` in the discriminant
range.

`hKΓ` is named, and it is not a formality: the descent theorem needs `ker ρ_bilin ≤ Γ`, while the
quadratic form `q` determines the bilinear one, so `ker ρ ≤ ker ρ_bilin` and the two kernels agree
only where `q` sees the form. The proof stops at the containment
`OrthogonalGroup.stableOrthogonalGroup coble_isFractionFieldPerfect ≤ cobleKernel`, which this
development neither proves nor refutes for `T_Co`. -/
noncomputable def cobleCuspOrbitsEquivDoubleCosetsPlane
    (hKΓ : OrthogonalGroup.stableOrthogonalGroup coble_isFractionFieldPerfect ≤
      cobleKernelSubgroup.toSubgroup)
    (N : PrimitiveIsotropic cobleLattice 2) :=
  cuspOrbitsEquivDoubleCosetsDiscriminant coble_isFractionFieldPerfect cobleKernelSubgroup hKΓ N

/-- The same statement at the exhibited Coble plane `coblePlane`. -/
noncomputable def cobleCuspOrbitsEquivDoubleCosetsCoblePlane
    (hKΓ : OrthogonalGroup.stableOrthogonalGroup coble_isFractionFieldPerfect ≤
      cobleKernelSubgroup.toSubgroup) :=
  cobleCuspOrbitsEquivDoubleCosetsPlane hKΓ coblePlane

end LeanCategories.Lattices.Valued
