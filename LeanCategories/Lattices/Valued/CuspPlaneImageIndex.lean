/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CuspPlaneLineCorrespondence
public import LeanCategories.Lattices.Valued.CuspWorkedInstance
public import LeanCategories.ForMathlib.ModularCuspsGL2

/-! # The plane stabilizer's image in `GL(2, ℤ)`: which finite-index question, and its verdict

`CuspPlaneLineCorrespondence` carries the plane stabilizer's image to a subgroup
`planeMatrixImage b ≤ GL(2, ℤ)` and identifies its orbits on `ℙ¹(ℚ)` with the stabilizer's orbits on
the primitive lines of `P`; its section "Step (d): the count is open" leaves the finite-index
hypothesis undecided. This module decides it, and decides which index the count actually needs.

## 1. The question, and the hypothesis on the restriction of the form to `P`

`PrimitiveIsotropic L 2` says that the form restricted to `P` **vanishes** (`isotropic`), so the
restriction is the zero form (`planeGramMatrix_eq_zero`) and in particular its Gram determinant is
`0`, not a unit (`planeGramMatrix_det_ne_unit`). `planeMatrixEquiv b` is therefore an equivalence
onto **all** of `GL(2, ℤ)`: `Aut(P)` is the full linear group of the plane, with no orthogonality
constraint, because every linear automorphism of the carrier preserves the zero form.

The only hypothesis that can be made on the restriction of the form to `P` inside this domain is
therefore "*it is zero*", and that hypothesis is already carried by the structure. Consequently:

* the image is constrained by the **lattice**, through which isometries of `L` preserve `P`, and not
  by the form on `P`;
* the case the issue raises as "the image can be finite, for a plane spanned by a unimodular
  summand" **cannot occur in this domain**: a plane whose Gram matrix is a unit-det matrix is not a
  `PrimitiveIsotropic` plane at all (`planeGramMatrix_det_ne_unit`). Its image is finite because it
  lands in the orthogonal group `O(P)` of a *nondegenerate* plane, not because of anything an
  isotropic plane can have.

## 2. The two candidate statements, and the lemma that separates them

Two indices are on offer for `planeMatrixImage b`: the index in `GL(2, ℤ)`, which is what
`natCard_cuspOrbits_le_index_GL2` consumes (`[Γ.FiniteIndex]` for `Γ ≤ GL(2, ℤ)`), or an index in
some finite group. They are not comparable, and the difference is not cosmetic: a finite subgroup of
a `GL(2, ℤ)` has **infinite** index there (`not_finiteIndex_of_finite`), because
`Subgroup.card_mul_index` makes a finite-index finite subgroup force the whole group finite and
`GL(2, ℤ)` is infinite (`unipotentGL_injective`). So "the image is finite, hence finite index
trivially" is true of the index in a finite stabilizer and **false** of the index in `GL(2, ℤ)`;
a plane with a finite image is exactly the plane where the two answers differ, and there the
`GL(2, ℤ)` answer is infinite index — which is the answer the corpus lemma cannot use.

The source's own `|F/S| = 8` for `T_Co` (`research-discriminant-descent-b636d06011.md`, line 443)
is an index of the *third* kind: `F` is `Stab_Q(J) ⊓ Stab_Q(C)` for `Q = O(A_L)` (line 128), the
orthogonal group of the **finite** discriminant group, and `S` is the image of the integral plane
stabilizer in it. `|F/S| = 8` therefore bounds no index in `GL(2, ℤ)` and no index of `GL(2, ℤ)`
bounds it; it is a statement that the discriminant image of the plane stabilizer misses a coset of
its own stabilizer, and it is the datum `F_{J,C}` of `CuspFlagFiniteness.lean:29` and
`CuspPlaneIncidence.lean:68`, not a finite-index statement. The source says the same in its own
words (line 107): *"The two input groups are genuinely different: `F` stabilizes a finite datum,
whereas `S` is the image of the actual integral stabilizer of the chosen object. Replacing `S` by
`F` silently asserts a lifting theorem."* What the source's shape does say — and what is right — is
that the group to index in must be the group the count is an orbit count for; for `#88`'s count that
group is `planeMatrixImage b ≤ GL(2, ℤ)`, because the corpus lemma is about subgroups of
`GL(2, ℤ)` and about no other group. So the acceptance's `|F/S| = 8` is **not** reproduced as an
instance of this statement and cannot be: `F` is finite and `S ≤ F`, so it is an index in a finite
group, while the statement decided here is an index in `GL(2, ℤ)`. Reproducing it needs
`ρ(Stab_{O(T_Co)}(P))` inside `Stab_Q(J)`, the source's `thm:coble-plane-stabilizer-image`; that
computation is not in the tree.

## 3. The verdict on the explicit planes

* **The split plane of `U ⊕ U`** (`splitPlane`, spanned by the two isotropic coordinates
  `e₁ = (1,0,0,0)` and `e₂ = (0,0,1,0)`). This is the smallest explicit plane in the tree, and the
  one whose complement is dual: `L = P ⊕ P^⊥` with the pairing `P × P^⊥ → ℤ` perfect. Every
  automorphism of `P` extends to an isometry of `L` — `e ↦ M e`, `f ↦ M^{-T} f` — so
  `planeStabilizerImage splitPlane = ⊤` (`planeStabilizerImage_splitPlane_eq_top`), and the image is
  all of `GL(2, ℤ)`: **index 1**, finite index with no hypothesis.
* **A plane whose image is thin**: no lattice in the tree has one, and the tree has no plane whose
  image is even computed besides the one above; the `T_Co` image is the page proof
  `thm:coble-plane-stabilizer-image` and is not in the tree in any form. The mathematics says none
  exists: for `P` totally isotropic, `Stab_{O(V)}(P_ℚ) → GL(P_ℚ)` is surjective — extend `A` by
  `A ⊕ id` on a maximal isotropic `W ⊇ P_ℚ` and by `A^{-T} ⊕ id` on `W^*` — so the image is the
  `ℤ`-points of a `ℚ`-subgroup it is Zariski-dense in, and Borel's theorem on images of arithmetic
  groups makes it commensurable with `GL(2, ℤ)`. **That theorem is not in this tree and is not
  reproved here**; the finite-index hypothesis is therefore a theorem to be imported or proved, not
  a counterexample to be exhibited. What *is* proved here is the split instance, index 1.

## 4. The count

`natCard_cuspOrbits_planeMatrixImage_le_index` is `#88`'s per-plane count read off from the corpus
lemma at the image subgroup — the statement of `#88` for `planeMatrixImage b` rather than for
`GL(2, ℤ)`, which the earlier module docstrings warned against — and at the split plane it gives
`≤ 1` (`natCard_cuspOrbits_splitPlane_le_one`). That bound is attained, since `GL(2, ℤ)` is
transitive on `ℙ¹(ℚ)`; the formal statement here is the bound, and the transitivity is not
formalized in this module.

`F_{J,C}` is **not** produced here: it is a subgroup of `O(A_L)`, the orthogonal group of the finite
discriminant group, and this module has no discriminant datum in it. What is missing for it is the
same thing that is missing for the source's `S`: a computation of the image of the plane stabilizer
in `O(A_L)` at `T_Co`.

## Search record (LC-09)

`scripts/formalization_corpus.py search` at the manifest head `9fdc1827` under `plane stabilizer
image finite index`, `finite subgroup has infinite index`, `Gram matrix vanishes on isotropic
submodule determinant` and `hyperbolic plane isometry stabilizer surjective general linear group`.
The hits are navigation-only: TauCeti's `NumberTheory/Modular/Stabilizer.lean` (orders of point
stabilizers of `SL(2, ℤ)` in `ℍ`), `TauCetiRoadmap` suggestion files, and an unrelated
`ImperialCollegeLondon/FLT` Krull-topology file. Nothing in the corpus states the finite index of a
plane-stabilizer image, and nothing states the split extension. The owners used are Mathlib's
`Subgroup.card_mul_index`, `Subgroup.map_top_of_surjective`, `Nat.card_eq_zero_of_infinite`,
`LinearMap.toMatrix_mulVec_repr`, `LinearMap.toMatrix_comp`, `Units.mkOfMulEqOne`, and the
repository's `planeStabilizerImage`, `planeStabilizerRestrict_apply_coe`, `planeMatrixEquiv`,
`twoHyperbolicPlanes`, `linearGroup`, `eCoord_hyperbolicLinearFn`, `fCoord_hyperbolicLinearFn`,
`finrank_map_of_injective`, `isPrimitiveSubmodule_iff_saturation_eq` and `mem_saturation_iff`.
Everything else is glue.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

/-! ## The restriction of the form to the plane is the zero form -/

section PlaneForm

attribute [local instance 10000] Submodule.module

variable {L : IntegralLatticeCat ℤ} {P : PrimitiveIsotropic L 2}

/-- **The Gram matrix of the plane in a basis**: the matrix of the restriction of the form to `P`.
This is the datum the finite-index question would have to be made conditional on. -/
noncomputable def planeGramMatrix (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => L.obj.pairing ((b i : ↥P.toSubmodule) : L.obj.carrier)
    ((b j : ↥P.toSubmodule) : L.obj.carrier)

/-- The restriction of the form to a `PrimitiveIsotropic` plane vanishes in every basis. -/
theorem planeGramMatrix_eq_zero (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    planeGramMatrix (P := P) b = 0 := by
  ext i j
  exact P.isotropic _ (b i).2 _ (b j).2

/-- Its determinant is zero. -/
theorem planeGramMatrix_det_eq_zero (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    (planeGramMatrix (P := P) b).det = 0 := by
  rw [planeGramMatrix_eq_zero]
  simp

/-- **A plane of this type is never unimodular.** The Gram determinant is `0`, so it is not a unit;
a plane spanned by a unimodular summand has unit determinant there, so it is not a
`PrimitiveIsotropic` plane. This is why the "finite image for a unimodular summand" case lies
outside the domain of the finite-index question rather than inside it. -/
theorem planeGramMatrix_det_ne_unit (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    ¬ IsUnit (planeGramMatrix (P := P) b).det := by
  rw [planeGramMatrix_det_eq_zero]
  exact not_isUnit_zero

/-- **Every matrix in `GL(2, ℤ)` is the matrix of some automorphism of the plane.** The form on `P`
vanishes, so it constrains nothing: the subgroup `planeMatrixImage b` is a subgroup of the whole
linear group of the plane, and the finite-index question is about the lattice only. -/
theorem exists_planeMatrixEquiv_eq (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (g : GL (Fin 2) ℤ) :
    ∃ δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule, planeMatrixEquiv b δ = g :=
  ⟨(planeMatrixEquiv b).symm g, (planeMatrixEquiv b).apply_symm_apply g⟩

end PlaneForm

/-! ## A finite image has infinite index in `GL(2, ℤ)` -/

section FiniteImage

open scoped MatrixGroups

attribute [local instance 10000] Submodule.module

/-- **A finite subgroup of an infinite group has infinite index.** `Subgroup.card_mul_index` is
`Nat.card H * H.index = Nat.card G`, and a finite `H` has nonzero card, so finite index plus finite
`H` forces `Nat.card G` nonzero, i.e. `G` finite. -/
theorem not_finiteIndex_of_finite {G : Type*} [Group G] [Infinite G]
    {H : Subgroup G} (hH : Finite H) : ¬ H.FiniteIndex := by
  intro hfi
  have hcard : Nat.card H ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, one_mem H⟩, hH⟩
  have hprod : Nat.card H * H.index ≠ 0 := Nat.mul_ne_zero hcard hfi.index_ne_zero
  rw [Subgroup.card_mul_index] at hprod
  exact hprod Nat.card_eq_zero_of_infinite

/-- The unipotent matrix `!![1, n; 0, 1]`. -/
def unipotentMat (n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, n; 0, 1]

/-- The unipotent matrix as an invertible integer matrix, its inverse being `!![1, -n; 0, 1]`. -/
def unipotentGL (n : ℤ) : GL (Fin 2) ℤ :=
  Units.mkOfMulEqOne (unipotentMat n) (unipotentMat (-n))
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [unipotentMat, Matrix.mul_apply, Fin.sum_univ_two])

@[simp]
theorem unipotentGL_val_apply (n : ℤ) :
    (unipotentGL n : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = n := by
  rw [unipotentGL, Units.val_mkOfMulEqOne]
  rfl

/-- The unipotent matrices are distinct, so `GL(2, ℤ)` is infinite. -/
theorem unipotentGL_injective : Function.Injective unipotentGL := by
  intro m n h
  have h' : (unipotentGL m : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
      (unipotentGL n : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by rw [h]
  simpa using h'

theorem generalLinearGroup_fin_two_int_infinite : Infinite (GL (Fin 2) ℤ) :=
  Infinite.of_injective unipotentGL unipotentGL_injective

/-- **A plane whose image in `GL(2, ℤ)` is finite has infinite index there.** This is the lemma that
separates the two candidate answers: the "finite image, so finite index trivially" reading is true
of an index in a finite group and false of the index the corpus count consumes. -/
theorem not_finiteIndex_of_finite_planeMatrixImage
    {L : IntegralLatticeCat ℤ} {P : PrimitiveIsotropic L 2}
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (h : Finite ↥(planeMatrixImage (P := P) b)) :
    ¬ (planeMatrixImage (P := P) b).FiniteIndex :=
  @not_finiteIndex_of_finite (GL (Fin 2) ℤ) _ generalLinearGroup_fin_two_int_infinite
    (planeMatrixImage (P := P) b) h

end FiniteImage

/-! ## The count from the finite-index statement

`#88`'s per-plane count, stated for the image subgroup rather than for `GL(2, ℤ)`. The finite-index
hypothesis is a hypothesis here and not a field of a structure, because this module does not prove
it for a general plane (see section 3 of the module docstring); the split plane below discharges it
unconditionally. -/

section Count

open scoped MatrixGroups

attribute [local instance 10000] Submodule.module

variable {L : IntegralLatticeCat ℤ} {P : PrimitiveIsotropic L 2}

/-- **The per-plane line count, from the finite-index statement.** If the image in `GL(2, ℤ)` has
finite index then it has at most `index` cusp orbits on `ℙ¹(ℚ)`, by
`natCard_cuspOrbits_le_index_GL2`. This is the statement `#88` needs, made for
`planeMatrixImage b` and not for `GL(2, ℤ)`. -/
theorem natCard_cuspOrbits_planeMatrixImage_le_index
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) [(planeMatrixImage (P := P) b).FiniteIndex] :
    Nat.card (_root_.CuspOrbits
      (LeanCategories.ForMathlib.gl2Image (planeMatrixImage (P := P) b))) ≤
      (planeMatrixImage (P := P) b).index :=
  LeanCategories.ForMathlib.natCard_cuspOrbits_le_index_GL2 _

end Count

/-! ## The split plane of `U ⊕ U`: the finite-index statement, proved with index `1`

`U ⊕ U` is the smallest lattice in the tree that carries a primitive isotropic *plane*, and its
standard plane — the one spanned by the two isotropic coordinates `e₁` and `e₂` — is the plane whose
complement is dual, `L = P ⊕ P^⊥` with `P^⊥/P` again a hyperbolic plane. Every automorphism of `P`
extends to an isometry there (`e ↦ M e` on the `E`-coordinates, `f ↦ M^{-T} f` on the
`F`-coordinates, which is `CuspWorkedInstance.linearGroup`), so the plane stabilizer's image is the
whole automorphism group of the plane. This is the verdict on the smallest explicit plane; the
count it gives is `≤ 1`. -/

section SplitPlane

attribute [local instance 10000] Submodule.module

/-- The `F`-coordinates of a vector of `U ⊕ U`, as a linear map. -/
def fCoordLin : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun := fCoord
  map_add' := fCoord_add
  map_smul' := fCoord_smul

/-- **The standard (split) plane of `U ⊕ U`**: the vectors whose `F`-coordinates vanish. -/
def splitPlaneSubmodule : Submodule ℤ (Fin 4 → ℤ) := LinearMap.ker fCoordLin

/-- Membership in the split plane, as the vanishing of the `F`-coordinates. -/
theorem mem_splitPlaneSubmodule {x : Fin 4 → ℤ} :
    x ∈ splitPlaneSubmodule ↔ fCoord x = 0 := Iff.rfl

/-- Membership in the split plane, in coordinates. -/
theorem mem_splitPlaneSubmodule_coord {x : Fin 4 → ℤ} :
    x ∈ splitPlaneSubmodule ↔ x 1 = 0 ∧ x 3 = 0 := by
  rw [mem_splitPlaneSubmodule]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h1, h3⟩
    funext j
    fin_cases j <;> simp [fCoord, h1, h3]

/-- The split plane is isotropic: the form pairs the `E`-part with the `F`-part. -/
theorem splitPlaneSubmodule_isotropic :
    IsIsotropicSubmodule twoHyperbolicPlanes splitPlaneSubmodule := by
  intro x hx y hy
  have hx' : fCoord x = 0 := hx
  have hy' : fCoord y = 0 := hy
  have hx1 : x 1 = 0 := congrFun hx' 0
  have hx3 : x 3 = 0 := congrFun hx' 1
  have hy1 : y 1 = 0 := congrFun hy' 0
  have hy3 : y 3 = 0 := congrFun hy' 1
  rw [IntegralLatticeCat.asBilinForm_apply]
  change x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 = 0
  rw [hx1, hx3, hy1, hy3]
  ring

/-- **The `E`-coordinates identify the split plane with `ℤ²`.** -/
def splitPlaneCoord : ↥splitPlaneSubmodule ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := eCoord (x : Fin 4 → ℤ)
  invFun v := ⟨![v 0, 0, v 1, 0], by
    rw [mem_splitPlaneSubmodule_coord]; exact ⟨rfl, rfl⟩⟩
  left_inv := by
    intro x
    refine Subtype.ext ?_
    obtain ⟨h1, h3⟩ := mem_splitPlaneSubmodule_coord.mp x.2
    funext j
    fin_cases j <;> simp [eCoord, h1, h3]
  right_inv := by
    intro v
    funext j
    fin_cases j <;> simp [eCoord]
  map_add' := by
    intro x y
    funext j
    fin_cases j <;> simp [eCoord]
  map_smul' := by
    intro r x
    funext j
    fin_cases j <;> simp [eCoord]

/-- The split plane has rank two. -/
theorem splitPlaneSubmodule_finrank : Module.finrank ℤ ↥splitPlaneSubmodule = 2 := by
  rw [LinearEquiv.finrank_eq splitPlaneCoord, Module.finrank_fintype_fun_eq_card]
  simp

/-- The split plane is primitive: a nonzero multiple of a vector cannot gain vanishing
`F`-coordinates. -/
theorem splitPlaneSubmodule_primitive : IsPrimitiveSubmodule splitPlaneSubmodule := by
  rw [isPrimitiveSubmodule_iff_saturation_eq]
  refine le_antisymm ?_ (le_saturation _)
  intro x hx
  obtain ⟨c, hc, hcx⟩ := (mem_saturation_iff (R := ℤ) splitPlaneSubmodule x).mp hx
  rw [mem_splitPlaneSubmodule] at hcx ⊢
  have hcx' : c • fCoord x = 0 := by
    rw [← fCoord_smul]; exact hcx
  exact (smul_eq_zero.mp hcx').resolve_left hc

/-- **The standard primitive isotropic plane of `U ⊕ U`.** -/
noncomputable def splitPlane : PrimitiveIsotropic twoHyperbolicPlanes 2 where
  toSubmodule := splitPlaneSubmodule
  isotropic := splitPlaneSubmodule_isotropic
  finrank_eq := splitPlaneSubmodule_finrank
  primitive := splitPlaneSubmodule_primitive

/-- The `E`-coordinates of the standard plane, read on the plane as a submodule of `L` (the same
equivalence as `splitPlaneCoord`, written against `splitPlane.toSubmodule` so that the plane's own
automorphisms compose with it without an unfolding step). -/
noncomputable def splitPlaneCoordL : ↥splitPlane.toSubmodule ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  splitPlaneCoord

/-- Two vectors of the split plane with the same `E`-coordinates are equal. -/
theorem splitPlane_ext {x y : Fin 4 → ℤ} (hx : x ∈ splitPlaneSubmodule)
    (hy : y ∈ splitPlaneSubmodule) (h : eCoord x = eCoord y) : x = y := by
  obtain ⟨hx1, hx3⟩ := mem_splitPlaneSubmodule_coord.mp hx
  obtain ⟨hy1, hy3⟩ := mem_splitPlaneSubmodule_coord.mp hy
  have h0 := congrFun h 0
  have h2 := congrFun h 1
  funext j
  fin_cases j <;> simp_all [eCoord]

/-- The matrix of a linear equivalence of `ℤ²`, applied to a vector, is its action through
`LinearMap.toMatrix` in the standard basis. -/
theorem toMatrix_mulVec_basisFun {ψ : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ)} (v : Fin 2 → ℤ) :
    (LinearMap.toMatrix (Pi.basisFun ℤ (Fin 2)) (Pi.basisFun ℤ (Fin 2)) ψ.toLinearMap).mulVec v =
      ψ v := by
  simp

/-- An invertible integer matrix acting on `ℤ²` kills a vector only at zero. -/
theorem mulVec_transpose_eq_zero_iff {M N : Matrix (Fin 2) (Fin 2) ℤ} (hNM : N * M = 1)
    (v : Fin 2 → ℤ) : (Matrix.transpose N).mulVec v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 : (Matrix.transpose M).mulVec ((Matrix.transpose N).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hNM, Matrix.transpose_one,
        Matrix.one_mulVec]
    rw [← h1, h, Matrix.mulVec_zero]
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- **The plane stabilizer's image at the split plane is the whole automorphism group of the
plane.** Every linear equivalence of the plane's carrier is realized by an isometry of `U ⊕ U`,
through the `GL₂(ℤ)` isometry `linearGroup` of `CuspWorkedInstance`. -/
theorem planeStabilizerImage_splitPlane_eq_top :
    planeStabilizerImage splitPlane = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr fun δ => ?_
  -- the matrix of `δ` in the `E`-coordinates
  set ψ : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    splitPlaneCoordL.symm.trans (δ.trans splitPlaneCoordL) with hψ
  set M : Matrix (Fin 2) (Fin 2) ℤ :=
    LinearMap.toMatrix (Pi.basisFun ℤ (Fin 2)) (Pi.basisFun ℤ (Fin 2)) ψ.toLinearMap with hM
  set N : Matrix (Fin 2) (Fin 2) ℤ :=
    LinearMap.toMatrix (Pi.basisFun ℤ (Fin 2)) (Pi.basisFun ℤ (Fin 2)) ψ.symm.toLinearMap with hN
  have hcomp₁ : ψ.toLinearMap.comp ψ.symm.toLinearMap = LinearMap.id := by
    ext x
    simp
  have hcomp₂ : ψ.symm.toLinearMap.comp ψ.toLinearMap = LinearMap.id := by
    ext x
    simp
  have hMN : M * N = 1 := by
    rw [hM, hN, ← LinearMap.toMatrix_comp (Pi.basisFun ℤ (Fin 2)) (Pi.basisFun ℤ (Fin 2))
      (Pi.basisFun ℤ (Fin 2)) ψ.toLinearMap ψ.symm.toLinearMap, hcomp₁, LinearMap.toMatrix_id]
  have hNM : N * M = 1 := by
    rw [hN, hM, ← LinearMap.toMatrix_comp (Pi.basisFun ℤ (Fin 2)) (Pi.basisFun ℤ (Fin 2))
      (Pi.basisFun ℤ (Fin 2)) ψ.symm.toLinearMap ψ.toLinearMap, hcomp₂, LinearMap.toMatrix_id]
  set g : OrthogonalGroup twoHyperbolicPlanes := linearGroup M N hMN hNM with hg
  have hE : ∀ x : Fin 4 → ℤ, eCoord (g.1.1 x) = M.mulVec (eCoord x) := by
    intro x
    rw [hg]
    exact eCoord_hyperbolicLinearFn M N x
  have hF : ∀ x : Fin 4 → ℤ,
      fCoord (g.1.1 x) = (Matrix.transpose N).mulVec (fCoord x) := by
    intro x
    rw [hg]
    exact fCoord_hyperbolicLinearFn M N x
  -- the isometry preserves the plane, and reflects membership in it
  have hplane_iff : ∀ x : Fin 4 → ℤ,
      g.1.1 x ∈ splitPlaneSubmodule ↔ x ∈ splitPlaneSubmodule := by
    intro x
    change fCoord (g.1.1 x) = 0 ↔ fCoord x = 0
    rw [hF x, mulVec_transpose_eq_zero_iff hNM]
  have hmap : splitPlaneSubmodule.map (g.1.toLinearMap) = splitPlaneSubmodule := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx' : ∃ y ∈ splitPlaneSubmodule, g.1.toLinearMap y = x := hx
      obtain ⟨y, hy, rfl⟩ := hx'
      exact (hplane_iff y).mpr hy
    · intro x hx
      have hx' : x ∈ splitPlaneSubmodule := hx
      have hsymm : g.1.toLinearMap (g.1.symm x) = x := LinearEquiv.apply_symm_apply g.1 x
      have hy : g.1.symm x ∈ splitPlaneSubmodule := by
        refine (hplane_iff (g.1.symm x)).mp ?_
        rw [hsymm]
        exact hx'
      have hmem := Submodule.mem_map_of_mem (f := g.1.toLinearMap) hy
      rw [hsymm] at hmem
      exact hmem
  have hmem : g ∈ MulAction.stabilizer (OrthogonalGroup twoHyperbolicPlanes) splitPlane := by
    rw [MulAction.mem_stabilizer_iff]
    refine PrimitiveIsotropic.ext ?_
    change splitPlane.toSubmodule.map (g.1.toLinearMap) = splitPlane.toSubmodule
    exact hmap
  refine ⟨⟨g, hmem⟩, ?_⟩
  refine LinearEquiv.ext fun x => Subtype.ext ?_
  change ((planeStabilizerRestrict (⟨g, hmem⟩ : ↥(MulAction.stabilizer
    (OrthogonalGroup twoHyperbolicPlanes) splitPlane)) x : ↥splitPlane.toSubmodule) :
      twoHyperbolicPlanes.obj.carrier) = (δ x : twoHyperbolicPlanes.obj.carrier)
  rw [planeStabilizerRestrict_apply_coe]
  change g.1.toLinearMap (x : twoHyperbolicPlanes.obj.carrier) =
    ((δ x : ↥splitPlane.toSubmodule) : twoHyperbolicPlanes.obj.carrier)
  refine splitPlane_ext ?_ ?_ ?_
  · exact (hplane_iff _).mpr x.2
  · exact (δ x).2
  · have hleft : eCoord (g.1.toLinearMap (x : twoHyperbolicPlanes.obj.carrier)) =
        M.mulVec (eCoord (x : twoHyperbolicPlanes.obj.carrier)) :=
      hE (x : twoHyperbolicPlanes.obj.carrier)
    have hψx : ψ (splitPlaneCoordL x) = splitPlaneCoordL (δ x) := by
      rw [hψ]
      simp [LinearEquiv.trans_apply]
    have hright : eCoord ((δ x : ↥splitPlane.toSubmodule) : twoHyperbolicPlanes.obj.carrier) =
        M.mulVec (eCoord (x : twoHyperbolicPlanes.obj.carrier)) := by
      have h1 : eCoord ((δ x : ↥splitPlane.toSubmodule) : twoHyperbolicPlanes.obj.carrier) =
          splitPlaneCoordL (δ x) := rfl
      rw [h1, ← hψx, toMatrix_mulVec_basisFun]
      rfl
    rw [hleft, hright]

/-- **The index of the plane stabilizer's image at the split plane is one**: the image is
everything, so the finite-index hypothesis the corpus count needs holds here without any hypothesis
on the plane. -/
theorem planeMatrixImage_splitPlane_eq_top
    (b : Module.Basis (Fin 2) ℤ ↥splitPlane.toSubmodule) :
    planeMatrixImage (P := splitPlane) b = ⊤ := by
  rw [planeMatrixImage, planeStabilizerImage_splitPlane_eq_top,
    Subgroup.map_top_of_surjective _ (planeMatrixEquiv b).surjective]

/-- The image at the split plane has finite index in `GL(2, ℤ)`. -/
theorem planeMatrixImage_splitPlane_finiteIndex
    (b : Module.Basis (Fin 2) ℤ ↥splitPlane.toSubmodule) :
    (planeMatrixImage (P := splitPlane) b).FiniteIndex := by
  rw [planeMatrixImage_splitPlane_eq_top]
  infer_instance

/-- The image at the split plane has index one: no coset survives. -/
theorem planeMatrixImage_splitPlane_index
    (b : Module.Basis (Fin 2) ℤ ↥splitPlane.toSubmodule) :
    (planeMatrixImage (P := splitPlane) b).index = 1 := by
  rw [planeMatrixImage_splitPlane_eq_top, Subgroup.index_top]

/-- **The count at the split plane**: the per-plane count of `#88` is at most one there, because the
image is all of `GL(2, ℤ)` and `GL(2, ℤ)` is transitive on `ℙ¹(ℚ)`. -/
theorem natCard_cuspOrbits_splitPlane_le_one
    (b : Module.Basis (Fin 2) ℤ ↥splitPlane.toSubmodule) :
    Nat.card (_root_.CuspOrbits
      (LeanCategories.ForMathlib.gl2Image (planeMatrixImage (P := splitPlane) b))) ≤ 1 := by
  calc Nat.card (_root_.CuspOrbits
        (LeanCategories.ForMathlib.gl2Image (planeMatrixImage (P := splitPlane) b)))
      ≤ (planeMatrixImage (P := splitPlane) b).index :=
        @natCard_cuspOrbits_planeMatrixImage_le_index twoHyperbolicPlanes splitPlane b
          (planeMatrixImage_splitPlane_finiteIndex b)
    _ = 1 := planeMatrixImage_splitPlane_index b

end SplitPlane

end LeanCategories.Lattices.Valued
