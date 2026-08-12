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

This file proves the compact-open property, the Haar measure, and the two-sided bound on the
volume. It does not prove that this subgroup is the stabilizer of the completed integral
lattice, and it does not prove any product formula.
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

/-- A basis of the local quadratic space. -/
noncomputable def localLatticeBasis (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Basis
      (Module.Free.ChooseBasisIndex (v.adicCompletion K)
        (LocalLattice K v L).obj.carrier)
      (v.adicCompletion K) (LocalLattice K v L).obj.carrier :=
  Module.Free.chooseBasis _ _

/-- The Gram matrix of the local quadratic space in the selected basis. -/
noncomputable abbrev localGramMatrix
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Matrix
      (Module.Free.ChooseBasisIndex (v.adicCompletion K)
        (LocalLattice K v L).obj.carrier)
      (Module.Free.ChooseBasisIndex (v.adicCompletion K)
        (LocalLattice K v L).obj.carrier)
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
