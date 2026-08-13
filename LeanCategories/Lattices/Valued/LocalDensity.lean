/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.AdelicClass
public import LeanCategories.Lattices.Valued.Completion

/-!
# Local densities of integral lattices

The quadratic space of a lattice is completed at one height-one place. Its orthogonal group is
locally compact, so it carries a Haar measure. In a selected basis, the isometries given by a
matrix and an inverse matrix with local integer entries form a compact open subgroup. Its Haar
volume is the local density at that place.

## The basis is a basis of the completed lattice

The local integers form a local ring and `L ⊗ O_v` is finite projective over them, hence free. A
basis of `L ⊗ O_v` becomes a basis of the local quadratic space after extension to the local
field, and that is the basis `localLatticeBasis` selected here. Integrality in it is therefore not
an artefact of a choice: `mem_localIntegralOrthogonalSubgroup_iff` reads the integral subgroup as
the stabilizer of `localIntegralLattice`, the completed integral lattice `O_v · L` inside the
local space. `mem_subringMatrixOrthogonalSubgroup_iff` is the general statement, for any subring
of coefficients and any basis of the ambient space.

This file proves the compact-open property, the Haar measure, the two-sided bound on the volume,
and the stabilizer description. It proves no product formula.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open LeanCategories.Modules.Bilinear.Valued
open scoped NumberField

namespace LeanCategories.Lattices.Valued

universe u w

section Subring

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable (S : Subring R) (I : Type w) [Fintype I] [DecidableEq I]

/-- Invertible matrices coming from a subring of coefficients. -/
def SubringGeneralLinearSubgroup :
    Subgroup (Matrix.GeneralLinearGroup I R) :=
  (Matrix.GeneralLinearGroup.map (n := I) S.subtype).range

omit [TopologicalSpace R] in
/-- A matrix is subring-integral exactly when it and its inverse have entries in the subring. -/
theorem mem_subringGeneralLinearSubgroup_iff
    (g : Matrix.GeneralLinearGroup I R) :
    g ∈ SubringGeneralLinearSubgroup S I ↔
      (g : Matrix I I R) ∈ (S : Set R).matrix ∧
        ((g⁻¹ : Matrix.GeneralLinearGroup I R) : Matrix I I R) ∈ (S : Set R).matrix := by
  constructor
  · rintro ⟨h, rfl⟩
    constructor <;> intro i j
    · exact (h i j).2
    · exact ((h⁻¹ : Matrix.GeneralLinearGroup I S) i j).2
  · rintro ⟨hg, hgInv⟩
    let A : Matrix I I S := fun i j => ⟨g i j, hg i j⟩
    let B : Matrix I I S := fun i j =>
      ⟨(g⁻¹ : Matrix.GeneralLinearGroup I R) i j, hgInv i j⟩
    have hf : Function.Injective (S.subtype) := Subtype.val_injective
    have hAf : Matrix.map A S.subtype = (g : Matrix I I R) := rfl
    have hBf : Matrix.map B S.subtype =
        ((g⁻¹ : Matrix.GeneralLinearGroup I R) : Matrix I I R) := rfl
    have hAB : A * B = 1 := by
      apply Matrix.map_injective hf
      change Matrix.map (A * B) S.subtype = Matrix.map 1 S.subtype
      simp only [Matrix.map_mul]
      rw [hAf, hBf]
      simp
    have hBA : B * A = 1 := by
      apply Matrix.map_injective hf
      change Matrix.map (B * A) S.subtype = Matrix.map 1 S.subtype
      simp only [Matrix.map_mul]
      rw [hBf, hAf]
      simp
    exact ⟨⟨A, B, hAB, hBA⟩, Units.val_injective rfl⟩

/-- An open subring gives an open group of integral invertible matrices. -/
theorem isOpen_subringGeneralLinearSubgroup (hS : IsOpen (S : Set R)) :
    IsOpen (SubringGeneralLinearSubgroup S I :
      Set (Matrix.GeneralLinearGroup I R)) := by
  have hset :
      (SubringGeneralLinearSubgroup S I :
          Set (Matrix.GeneralLinearGroup I R)) =
        {g : Matrix.GeneralLinearGroup I R |
          (g : Matrix I I R) ∈ (S : Set R).matrix ∧
            ((g⁻¹ : Matrix.GeneralLinearGroup I R) : Matrix I I R) ∈
              (S : Set R).matrix} :=
    Set.ext fun g => mem_subringGeneralLinearSubgroup_iff S I g
  rw [hset]
  exact (hS.matrix.preimage Units.continuous_val).inter
    (hS.matrix.preimage Units.continuous_coe_inv)

/-- A compact subring gives a compact group of integral invertible matrices. -/
theorem isCompact_subringGeneralLinearSubgroup [IsTopologicalRing R] [T2Space R]
    [CompactSpace S] :
    IsCompact (SubringGeneralLinearSubgroup S I :
      Set (Matrix.GeneralLinearGroup I R)) := by
  letI : CompactSpace (Matrix I I S) := Pi.compactSpace
  change IsCompact (Set.range (Matrix.GeneralLinearGroup.map (n := I) S.subtype))
  rw [← Set.image_univ]
  exact isCompact_univ.image continuous_subtype_val.generalLinearGroup_map

variable {I}

/-- Integral matrices inside the orthogonal group of a Gram matrix. -/
abbrev SubringMatrixOrthogonalSubgroup (B : Matrix I I R) :
    Subgroup (MatrixOrthogonalGroup B) :=
  (SubringGeneralLinearSubgroup S I).comap (MatrixOrthogonalGroup B).subtype

/-- Integral orthogonal matrices form an open subgroup. -/
theorem isOpen_subringMatrixOrthogonalSubgroup (hS : IsOpen (S : Set R))
    (B : Matrix I I R) :
    IsOpen (SubringMatrixOrthogonalSubgroup S B : Set (MatrixOrthogonalGroup B)) :=
  (isOpen_subringGeneralLinearSubgroup S I hS).preimage continuous_subtype_val

/-- Integral orthogonal matrices form a compact subgroup. -/
theorem isCompact_subringMatrixOrthogonalSubgroup [IsTopologicalRing R] [T2Space R]
    [CompactSpace S] (B : Matrix I I R) :
    IsCompact (SubringMatrixOrthogonalSubgroup S B :
      Set (MatrixOrthogonalGroup B)) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have hset :
      ((fun g : MatrixOrthogonalGroup B =>
          (g : Matrix.GeneralLinearGroup I R)) ''
        (SubringMatrixOrthogonalSubgroup S B : Set (MatrixOrthogonalGroup B))) =
      (SubringGeneralLinearSubgroup S I :
          Set (Matrix.GeneralLinearGroup I R)) ∩
        (MatrixOrthogonalGroup B : Set (Matrix.GeneralLinearGroup I R)) := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨hh, h.property⟩
    · rintro ⟨hg, hB⟩
      exact ⟨⟨g, hB⟩, hg, rfl⟩
  rw [hset]
  exact (isCompact_subringGeneralLinearSubgroup S I).inter_right
    (matrixOrthogonalGroup_isClosed B)

end Subring

section BasisLattice

variable {F : Type u} [Field F] (S : Subring F)
variable {I : Type w}
variable (L : IntegralLatticeCat F) (b : Module.Basis I F L.obj.carrier)

/-- The `S`-lattice spanned by a basis of the ambient quadratic space. -/
def basisLattice : Submodule S L.obj.carrier :=
  Submodule.span S (Set.range b)

/-- A vector lies in the `S`-lattice of a basis exactly when its coordinates are `S`-integral. -/
theorem mem_basisLattice_iff (x : L.obj.carrier) :
    x ∈ basisLattice S L b ↔ ∀ i, b.repr x i ∈ S := by
  rw [basisLattice, Module.Basis.mem_span_iff_repr_mem S b x]
  refine forall_congr' fun i ↦ ?_
  constructor
  · rintro ⟨s, hs⟩
    exact hs ▸ s.2
  · exact fun h ↦ ⟨⟨_, h⟩, rfl⟩

/-- A basis vector lies in the lattice it spans. -/
theorem basis_mem_basisLattice (i : I) : b i ∈ basisLattice S L b :=
  Submodule.subset_span ⟨i, rfl⟩

/-- An `F`-linear automorphism carries the basis lattice into itself exactly when its matrix in
that basis is `S`-integral: the entries of the matrix are the coordinates of the images of the
basis vectors. -/
theorem toMatrix_mem_matrix_iff [Fintype I] [DecidableEq I]
    (g : L.obj.carrier ≃ₗ[F] L.obj.carrier) :
    LinearMap.toMatrix b b g.toLinearMap ∈ (S : Set F).matrix ↔
      ∀ x ∈ basisLattice S L b, g x ∈ basisLattice S L b := by
  constructor
  · intro hg x hx
    rw [mem_basisLattice_iff] at hx
    have hbasis : ∀ j, g (b j) ∈ basisLattice S L b := by
      intro j
      rw [mem_basisLattice_iff]
      intro i
      simpa [LinearMap.toMatrix_apply] using hg i j
    have hx' : x = ∑ j, b.repr x j • b j := (b.sum_repr x).symm
    rw [hx', map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem _ (⟨b.repr x j, hx j⟩ : S) (hbasis j)
  · intro hg i j
    have hbj := hg (b j) (basis_mem_basisLattice S L b j)
    rw [mem_basisLattice_iff] at hbj
    simpa [LinearMap.toMatrix_apply] using hbj i

/-- The matrix presentation of an isometry is its matrix in the selected basis. -/
theorem orthogonalGroupMatrixEquiv_coe_coe [Fintype I] [DecidableEq I]
    (g : BilinModuleCat.OrthogonalGroup L.obj) :
    ((orthogonalGroupMatrixEquiv L b g : MatrixOrthogonalGroup (gramMatrix L b)) :
        Matrix.GeneralLinearGroup I F) = linearEquivMatrixEquiv L b g.1 :=
  rfl

/-- **The integral orthogonal subgroup is the stabilizer of the basis lattice.** An isometry of the
ambient quadratic space is `S`-integral in a basis exactly when it carries the `S`-lattice spanned
by that basis onto itself. Both the isometry and its inverse must preserve the lattice, which is
what integrality of the matrix together with integrality of its inverse says. -/
theorem mem_subringMatrixOrthogonalSubgroup_iff [Fintype I] [DecidableEq I]
    (g : BilinModuleCat.OrthogonalGroup L.obj) :
    orthogonalGroupMatrixEquiv L b g ∈ SubringMatrixOrthogonalSubgroup S (gramMatrix L b) ↔
      (g.1 : L.obj.carrier → L.obj.carrier) '' (basisLattice S L b : Set L.obj.carrier) =
        basisLattice S L b := by
  have hmat : (((MatrixOrthogonalGroup (gramMatrix L b)).subtype
      (orthogonalGroupMatrixEquiv L b g) : Matrix.GeneralLinearGroup I F) : Matrix I I F) =
      LinearMap.toMatrix b b g.1.toLinearMap := rfl
  have hmatinv : ((((MatrixOrthogonalGroup (gramMatrix L b)).subtype
      (orthogonalGroupMatrixEquiv L b g))⁻¹ : Matrix.GeneralLinearGroup I F) : Matrix I I F) =
      LinearMap.toMatrix b b g.1.symm.toLinearMap := rfl
  rw [Subgroup.mem_comap, mem_subringGeneralLinearSubgroup_iff, hmat, hmatinv,
    toMatrix_mem_matrix_iff, toMatrix_mem_matrix_iff]
  constructor
  · rintro ⟨hforward, hbackward⟩
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hforward x hx
    · intro x hx
      exact ⟨g.1.symm x, hbackward x hx, g.1.apply_symm_apply x⟩
  · intro himage
    constructor
    · intro x hx
      exact himage.subset (Set.mem_image_of_mem _ hx)
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := himage.symm.subset hx
      rw [← hyx, g.1.symm_apply_apply]
      exact hy

end BasisLattice

section Local

variable (K : Type u) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The valuation subring of a height-one completion, as a subring of the local field. -/
abbrev localIntegers : Subring (v.adicCompletion K) :=
  (v.adicCompletionIntegers K).toSubring

/-- The local integer subring is open in the local field. -/
theorem isOpen_localIntegers :
    IsOpen (localIntegers K v : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring (v.adicCompletion K)

/-- The local integer subring is compact. -/
instance compactSpaceLocalIntegers : CompactSpace (localIntegers K v) :=
  HeightOneSpectrum.compactSpaceAdicCompletionIntegers K v

/-- The local quadratic space of an integral lattice at a height-one place. -/
abbrev LocalLattice (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  (extendIntegralToHeightOneField (𝓞 K) K v).obj L.obj

/-- Completion at a place preserves finite generation. -/
instance localLatticeFinite (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Finite (v.adicCompletion K) (LocalLattice K v L).obj.carrier := by
  letI : Module.Finite (𝓞 K) L.obj.obj.carrier := L.property
  change Module.Finite (v.adicCompletion K)
    (TensorProduct (𝓞 K) (v.adicCompletion K) L.obj.obj.carrier)
  infer_instance

/-- The orthogonal group of the completed local quadratic space. -/
abbrev LocalOrthogonalGroup (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup (LocalLattice K v L).obj

/-- Scalars from the number ring reach the local field through the local integers. -/
instance localIntegersScalarTower :
    IsScalarTower (𝓞 K) (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The completed integral lattice `L ⊗ O_v` at a height-one place. -/
abbrev CompletedIntegralLattice (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  TensorProduct (𝓞 K) (v.adicCompletionIntegers K) L.obj.obj.carrier

/-- The completed integral lattice is finite over the local integers. -/
instance completedIntegralLatticeFinite (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Finite (v.adicCompletionIntegers K) (CompletedIntegralLattice K v L) := by
  letI : Module.Finite (𝓞 K) L.obj.obj.carrier := L.property
  infer_instance

/-- The completed integral lattice is free, because the local integers form a local ring and the
lattice is finite projective over them. -/
instance completedIntegralLatticeFree (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Free (v.adicCompletionIntegers K) (CompletedIntegralLattice K v L) := by
  letI : Module.Finite (𝓞 K) L.obj.obj.carrier := L.property
  letI : Module.Projective (𝓞 K) L.obj.obj.carrier := L.obj.property.1
  infer_instance

/-- The index of a chosen basis of the completed integral lattice. -/
abbrev CompletedIntegralBasisIndex (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  Module.Free.ChooseBasisIndex (v.adicCompletionIntegers K) (CompletedIntegralLattice K v L)

/-- A basis of the completed integral lattice over the local integers. -/
noncomputable def completedIntegralLatticeBasis (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Basis (CompletedIntegralBasisIndex K v L) (v.adicCompletionIntegers K)
      (CompletedIntegralLattice K v L) :=
  Module.Free.chooseBasis _ _

/-- The local quadratic space is the local field extension of the completed integral lattice. -/
noncomputable def completedIntegralLatticeBaseChange
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (v.adicCompletionIntegers K) (v.adicCompletion K)
        (CompletedIntegralLattice K v L) ≃ₗ[v.adicCompletion K]
      (LocalLattice K v L).obj.carrier :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (v.adicCompletionIntegers K)
    (v.adicCompletion K) (v.adicCompletion K) L.obj.obj.carrier

/-- A basis of the completed integral lattice, carried into the local quadratic space. It is a
basis of that space over the local field. -/
noncomputable def completedIntegralBasis (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Basis (CompletedIntegralBasisIndex K v L) (v.adicCompletion K)
      (LocalLattice K v L).obj.carrier :=
  ((completedIntegralLatticeBasis K v L).baseChange (v.adicCompletion K)).map
    (completedIntegralLatticeBaseChange K v L)

/-- The completed integral lattice sits inside the local quadratic space. -/
noncomputable def completedIntegralInclusion (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    CompletedIntegralLattice K v L →ₗ[v.adicCompletionIntegers K]
      (LocalLattice K v L).obj.carrier :=
  (completedIntegralLatticeBaseChange K v L).restrictScalars (v.adicCompletionIntegers K) ∘ₗ
    (TensorProduct.mk (v.adicCompletionIntegers K) (v.adicCompletion K)
      (CompletedIntegralLattice K v L) 1)

@[simp]
theorem completedIntegralInclusion_tmul (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a : v.adicCompletionIntegers K) (x : L.obj.obj.carrier) :
    completedIntegralInclusion K v L (a ⊗ₜ[𝓞 K] x) =
      (a : v.adicCompletion K) ⊗ₜ[𝓞 K] x := by
  show TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (v.adicCompletionIntegers K)
      (v.adicCompletion K) (v.adicCompletion K) L.obj.obj.carrier
      ((1 : v.adicCompletion K) ⊗ₜ[v.adicCompletionIntegers K] (a ⊗ₜ[𝓞 K] x)) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  congr 1
  simp [Algebra.smul_def]

@[simp]
theorem completedIntegralInclusion_basis (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (i : CompletedIntegralBasisIndex K v L) :
    completedIntegralInclusion K v L (completedIntegralLatticeBasis K v L i) =
      completedIntegralBasis K v L i := by
  simp [completedIntegralInclusion, completedIntegralBasis]

/-- **The completed integral lattice inside the local quadratic space**: the local integers times
the image of `L`. -/
def localIntegralLattice (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Submodule (localIntegers K v) (LocalLattice K v L).obj.carrier :=
  Submodule.span (localIntegers K v)
    (Set.range fun x : L.obj.obj.carrier ↦
      ((1 : v.adicCompletion K) ⊗ₜ[𝓞 K] x : (LocalLattice K v L).obj.carrier))

/-- A pure tensor with an integral scalar lies in the completed integral lattice. -/
theorem tmul_mem_localIntegralLattice (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a : v.adicCompletionIntegers K) (x : L.obj.obj.carrier) :
    ((a : v.adicCompletion K) ⊗ₜ[𝓞 K] x : (LocalLattice K v L).obj.carrier) ∈
      localIntegralLattice K v L := by
  have hmem : ((1 : v.adicCompletion K) ⊗ₜ[𝓞 K] x : (LocalLattice K v L).obj.carrier) ∈
      localIntegralLattice K v L := Submodule.subset_span ⟨x, rfl⟩
  have hsmul := Submodule.smul_mem (localIntegralLattice K v L)
    (⟨(a : v.adicCompletion K), a.2⟩ : localIntegers K v) hmem
  have heq :
      ((a : v.adicCompletion K) • ((1 : v.adicCompletion K) ⊗ₜ[𝓞 K] x) :
        TensorProduct (𝓞 K) (v.adicCompletion K) L.obj.obj.carrier) =
      (a : v.adicCompletion K) ⊗ₜ[𝓞 K] x := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact heq ▸ hsmul

/-- The completed integral lattice is the image of the completed lattice `L ⊗ O_v`. -/
theorem completedIntegralInclusion_mem (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (w : CompletedIntegralLattice K v L) :
    completedIntegralInclusion K v L w ∈ localIntegralLattice K v L := by
  induction w using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | tmul a x =>
    rw [completedIntegralInclusion_tmul]
    exact tmul_mem_localIntegralLattice K v L a x
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Every element of the completed lattice `L ⊗ O_v` lands in the lattice spanned by the adapted
basis: expand it in that basis and apply the inclusion. -/
theorem completedIntegralInclusion_mem_basisLattice
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) (w : CompletedIntegralLattice K v L) :
    completedIntegralInclusion K v L w ∈
      basisLattice (localIntegers K v) (LocalLattice K v L) (completedIntegralBasis K v L) := by
  classical
  rw [← (completedIntegralLatticeBasis K v L).sum_repr w, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_smul, completedIntegralInclusion_basis]
  exact Submodule.smul_mem _
    (⟨((completedIntegralLatticeBasis K v L).repr w i : v.adicCompletion K),
      ((completedIntegralLatticeBasis K v L).repr w i).2⟩ : localIntegers K v)
    (basis_mem_basisLattice _ _ _ i)

/-- **The integral orthogonal subgroup stabilizes the completed integral lattice.** The lattice
spanned by the adapted basis is the completed integral lattice `L ⊗ O_v` itself. -/
theorem localIntegralLattice_eq_basisLattice (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    localIntegralLattice K v L =
      basisLattice (localIntegers K v) (LocalLattice K v L) (completedIntegralBasis K v L) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨x, rfl⟩
    have hx := completedIntegralInclusion_mem_basisLattice K v L ((1 : v.adicCompletionIntegers K)
      ⊗ₜ[𝓞 K] x)
    rwa [completedIntegralInclusion_tmul, OneMemClass.coe_one] at hx
  · rintro _ ⟨i, rfl⟩
    rw [← completedIntegralInclusion_basis]
    exact completedIntegralInclusion_mem K v L _

/-- The basis of the local quadratic space used throughout: a basis of the completed integral
lattice, so that integrality in this basis is integrality against `L ⊗ O_v`. -/
noncomputable def localLatticeBasis (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Basis (CompletedIntegralBasisIndex K v L)
      (v.adicCompletion K) (LocalLattice K v L).obj.carrier :=
  completedIntegralBasis K v L

/-- The Gram matrix of the local quadratic space in the selected basis. -/
noncomputable abbrev localGramMatrix
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Matrix (CompletedIntegralBasisIndex K v L) (CompletedIntegralBasisIndex K v L)
      (v.adicCompletion K) :=
  gramMatrix (LocalLattice K v L) (localLatticeBasis K v L)

/-- The local orthogonal-group topology from a basis presentation. -/
noncomputable instance localOrthogonalGroupTopology
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TopologicalSpace (LocalOrthogonalGroup K v L) :=
  orthogonalGroupTopology _ (localLatticeBasis K v L)

/-- The selected basis gives a homeomorphism to the matrix orthogonal group. -/
noncomputable def localOrthogonalHomeomorph
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    LocalOrthogonalGroup K v L ≃ₜ MatrixOrthogonalGroup (localGramMatrix K v L) :=
  (orthogonalGroupMatrixEquiv _ (localLatticeBasis K v L)).toEquiv
    |>.toHomeomorphOfIsInducing ⟨rfl⟩

/-- The local orthogonal group is a topological group. -/
noncomputable instance localOrthogonalGroupIsTopologicalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    IsTopologicalGroup (LocalOrthogonalGroup K v L) :=
  orthogonalGroup_isTopologicalGroup _ (localLatticeBasis K v L)

/-- The local orthogonal group is locally compact. -/
noncomputable instance localOrthogonalGroupLocallyCompactSpace
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    LocallyCompactSpace (LocalOrthogonalGroup K v L) :=
  orthogonalGroupLocallyCompactSpace _ (localLatticeBasis K v L)

/-- The local isometries that are integral in the selected basis. -/
abbrev LocalIntegralOrthogonalSubgroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Subgroup (LocalOrthogonalGroup K v L) :=
  (SubringMatrixOrthogonalSubgroup (localIntegers K v)
    (localGramMatrix K v L)).comap
      (orthogonalGroupMatrixEquiv _ (localLatticeBasis K v L)).toMonoidHom

set_option maxRecDepth 4000 in
/-- **The local integral orthogonal subgroup is the stabilizer of the completed integral lattice.**
Integrality of the matrix and of its inverse in the selected basis says exactly that the isometry
carries `L ⊗ O_v` onto itself, because the selected basis is a basis of `L ⊗ O_v`. -/
theorem mem_localIntegralOrthogonalSubgroup_iff
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) (g : LocalOrthogonalGroup K v L) :
    g ∈ LocalIntegralOrthogonalSubgroup K v L ↔
      (g.1 : (LocalLattice K v L).obj.carrier → (LocalLattice K v L).obj.carrier) ''
          (localIntegralLattice K v L : Set (LocalLattice K v L).obj.carrier) =
        localIntegralLattice K v L := by
  rw [localIntegralLattice_eq_basisLattice]
  exact mem_subringMatrixOrthogonalSubgroup_iff (localIntegers K v) (LocalLattice K v L)
    (localLatticeBasis K v L) g

/-- The integral subgroup is open in the local orthogonal group. -/
theorem isOpen_localIntegralOrthogonalSubgroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    IsOpen (LocalIntegralOrthogonalSubgroup K v L :
      Set (LocalOrthogonalGroup K v L)) :=
  (isOpen_subringMatrixOrthogonalSubgroup _ (isOpen_localIntegers K v) _).preimage
    (localOrthogonalHomeomorph K v L).continuous

/-- The integral subgroup is compact. -/
theorem isCompact_localIntegralOrthogonalSubgroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    IsCompact (LocalIntegralOrthogonalSubgroup K v L :
      Set (LocalOrthogonalGroup K v L)) :=
  (localOrthogonalHomeomorph K v L).isCompact_preimage.mpr
    (isCompact_subringMatrixOrthogonalSubgroup _ _)

/-- Haar measure on the local orthogonal group. -/
noncomputable def localHaarMeasure
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    @MeasureTheory.Measure (LocalOrthogonalGroup K v L)
      (@borel (LocalOrthogonalGroup K v L) (localOrthogonalGroupTopology K v L)) :=
  orthogonalGroupHaarMeasure _ (localLatticeBasis K v L)

/-- The Haar volume of the integral subgroup at one height-one place. This is the local factor
of a Siegel mass formula. The product formula that relates these local factors to the global
mass of the genus of the lattice is NOT proved here. The identification of this subgroup with
the stabilizer of the completed integral lattice is also not proved here. -/
noncomputable def localDensity
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) : ENNReal := by
  letI : MeasurableSpace (LocalOrthogonalGroup K v L) := borel _
  exact localHaarMeasure K v L (LocalIntegralOrthogonalSubgroup K v L)

/-- The local density is positive, because the integral subgroup is open. -/
theorem localDensity_pos (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    0 < localDensity K v L := by
  letI : MeasurableSpace (LocalOrthogonalGroup K v L) := borel _
  let μ := localHaarMeasure K v L
  letI : μ.IsHaarMeasure := by
    dsimp [μ, localHaarMeasure, orthogonalGroupHaarMeasure]
    infer_instance
  exact (isOpen_localIntegralOrthogonalSubgroup K v L).measure_pos μ
    ⟨1, Subgroup.one_mem _⟩

/-- The local density is finite, because the integral subgroup is compact. -/
theorem localDensity_ne_top (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    localDensity K v L ≠ ⊤ := by
  letI : MeasurableSpace (LocalOrthogonalGroup K v L) := borel _
  let μ := localHaarMeasure K v L
  letI : μ.IsHaarMeasure := by
    dsimp [μ, localHaarMeasure, orthogonalGroupHaarMeasure]
    infer_instance
  exact (isCompact_localIntegralOrthogonalSubgroup K v L).measure_lt_top.ne

end Local

end LeanCategories.Lattices.Valued
