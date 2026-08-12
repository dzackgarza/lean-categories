/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Adele
public import LeanCategories.Lattices.Valued.TopologicalOrthogonalGroup
public import LeanCategories.ForMathlib.AdicCompletionLocallyCompact
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Finite adelic classes of integral lattices

The ambient quadratic space is first extended from the integer ring to its number field.
Its orthogonal group is then extended to the finite adele ring. This presentation gives the
diagonal rational subgroup without a choice of basis.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open LeanCategories.Modules.Bilinear.Valued
open scoped NumberField
open scoped Pointwise
open scoped RestrictedProduct

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A selected finite place, obtained from a maximal ideal of the number ring. -/
noncomputable def numberRingFinitePlace : HeightOneSpectrum (𝓞 K) := by
  let h := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField K)
  let p := Classical.choose h
  exact HeightOneSpectrum.mk p (Classical.choose_spec h).2.isPrime
    (Classical.choose_spec h).1

/-- The finite adele ring of a number field is nontrivial. -/
instance finiteAdeleRingNontrivial : Nontrivial (FiniteAdeleRing (𝓞 K) K) :=
  by
    refine ⟨0, 1, ?_⟩
    intro h
    let v : HeightOneSpectrum (𝓞 K) := numberRingFinitePlace K
    have hv := congrArg (fun a : FiniteAdeleRing (𝓞 K) K => a v) h
    exact zero_ne_one hv

/-- The finite adele topology is Hausdorff because every local completion is Hausdorff. -/
instance finiteAdeleRingT2Space : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  by
    change T2Space (Πʳ v : HeightOneSpectrum (𝓞 K),
      [v.adicCompletion K, v.adicCompletionIntegers K])
    infer_instance

/-- The finite adele ring of a number field is locally compact. -/
instance finiteAdeleRingLocallyCompactSpace :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by
  change LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum (𝓞 K),
      [v.adicCompletion K, v.adicCompletionIntegers K])
  letI : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  apply RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
  filter_upwards [] with v
  exact isCompact_iff_compactSpace.mpr
    (HeightOneSpectrum.compactSpaceAdicCompletionIntegers K v)

/-- Scalar multiplication by the number field on its finite adeles is faithful. -/
instance finiteAdeleRingFaithfulSMul : FaithfulSMul K (FiniteAdeleRing (𝓞 K) K) where
  eq_of_smul_eq_smul h := by
    simpa [Algebra.smul_def] using h (1 : FiniteAdeleRing (𝓞 K) K)

/-- The rational quadratic space attached to an integral lattice. -/
abbrev NumberFieldRationalLattice
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  (baseChangeIntegral (𝓞 K) K).obj L.obj

/-- Rationalization preserves finite generation. -/
noncomputable instance numberFieldRationalLatticeFinite
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Finite K (NumberFieldRationalLattice K L).obj.carrier := by
  letI : Module.Finite (𝓞 K) L.obj.obj.carrier := L.property
  change Module.Finite K (TensorProduct (𝓞 K) K L.obj.obj.carrier)
  infer_instance

/-- The rational orthogonal group of an integral lattice. -/
abbrev RationalOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup (NumberFieldRationalLattice K L).obj

/-- The finite adelic orthogonal group of the rational quadratic space. -/
abbrev RationalFiniteAdelicOrthogonalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  BilinModuleCat.OrthogonalGroup
    ((baseChangeIntegral K (FiniteAdeleRing (𝓞 K) K)).obj
      (NumberFieldRationalLattice K L)).obj

/-- A basis of the rational quadratic space. -/
noncomputable def rationalLatticeBasis
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Basis
      (Module.Free.ChooseBasisIndex K (NumberFieldRationalLattice K L).obj.carrier)
      K (NumberFieldRationalLattice K L).obj.carrier :=
  Module.Free.chooseBasis K _

/-- The induced basis of the finite adelic quadratic space. -/
noncomputable def rationalFiniteAdeleBasis
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Module.Basis
      (Module.Free.ChooseBasisIndex K (NumberFieldRationalLattice K L).obj.carrier)
      (FiniteAdeleRing (𝓞 K) K)
      ((baseChangeIntegral K (FiniteAdeleRing (𝓞 K) K)).obj
        (NumberFieldRationalLattice K L)).obj.carrier :=
  (rationalLatticeBasis K L).baseChange (FiniteAdeleRing (𝓞 K) K)

/-- The finite adelic orthogonal-group topology from a basis presentation. -/
noncomputable instance rationalFiniteAdelicOrthogonalGroupTopology
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TopologicalSpace (RationalFiniteAdelicOrthogonalGroup K L) :=
  orthogonalGroupTopology _ (rationalFiniteAdeleBasis K L)

/-- The finite adelic orthogonal group is a topological group. -/
noncomputable instance rationalFiniteAdelicOrthogonalGroupIsTopologicalGroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    IsTopologicalGroup (RationalFiniteAdelicOrthogonalGroup K L) :=
  orthogonalGroup_isTopologicalGroup _ (rationalFiniteAdeleBasis K L)

/-- The finite adelic orthogonal group is locally compact. -/
noncomputable instance rationalFiniteAdelicOrthogonalGroupLocallyCompactSpace
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    LocallyCompactSpace (RationalFiniteAdelicOrthogonalGroup K L) :=
  orthogonalGroupLocallyCompactSpace _ (rationalFiniteAdeleBasis K L)

/-- Haar measure on the finite adelic orthogonal group. -/
noncomputable def rationalFiniteAdelicOrthogonalGroupHaarMeasure
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    @MeasureTheory.Measure (RationalFiniteAdelicOrthogonalGroup K L)
      (@borel (RationalFiniteAdelicOrthogonalGroup K L)
        (rationalFiniteAdelicOrthogonalGroupTopology K L)) := by
  letI : MeasurableSpace (RationalFiniteAdelicOrthogonalGroup K L) := borel _
  letI : BorelSpace (RationalFiniteAdelicOrthogonalGroup K L) := ⟨rfl⟩
  exact MeasureTheory.Measure.haar

/-- Scalar extension gives the diagonal rational subgroup in the finite adelic group. -/
noncomputable def rationalFiniteAdeleOrthogonalHom
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    RationalOrthogonalGroup K L →*
      RationalFiniteAdelicOrthogonalGroup K L :=
  orthogonalGroupBaseChangeHom (R := K) (FiniteAdeleRing (𝓞 K) K)
    (NumberFieldRationalLattice K L)

/-- The diagonal map on rational orthogonal groups is injective. -/
theorem rationalFiniteAdeleOrthogonalHom_injective
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Function.Injective (rationalFiniteAdeleOrthogonalHom K L) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun e => e.1 (1 ⊗ₜ[K] x)) hgh
  simpa using Module.Flat.tensorProduct_mk_injective K
    (NumberFieldRationalLattice K L).obj.carrier
    (FiniteAdeleRing (𝓞 K) K) hx

/-- The image of the rational orthogonal group under the diagonal map. -/
abbrev RationalFiniteAdeleOrthogonalSubgroup
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Subgroup (RationalFiniteAdelicOrthogonalGroup K L) :=
  (rationalFiniteAdeleOrthogonalHom K L).range

/-- The finite adelic orthogonal group acts on its quadratic space. -/
instance rationalFiniteAdelicOrthogonalGroupMulAction
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    MulAction (RationalFiniteAdelicOrthogonalGroup K L)
      ((baseChangeIntegral K (FiniteAdeleRing (𝓞 K) K)).obj
        (NumberFieldRationalLattice K L)).obj.carrier where
  smul g x := g.1 x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The integral finite adelic lattice inside the adelization of the rational space. -/
def rationalFiniteIntegralAdeleLattice
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    Set ((baseChangeIntegral K (FiniteAdeleRing (𝓞 K) K)).obj
      (NumberFieldRationalLattice K L)).obj.carrier :=
  Set.range fun x :
      TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier =>
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (𝓞 K) K (FiniteAdeleRing (𝓞 K) K)
      (FiniteAdeleRing (𝓞 K) K) L.obj.obj.carrier).symm
        (finiteIntegralAdeleLatticeMap K L x)

/-- The stabilizer of the integral finite adelic lattice. -/
abbrev RationalFiniteIntegralAdeleLatticeStabilizer
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  MulAction.stabilizer (RationalFiniteAdelicOrthogonalGroup K L)
    (rationalFiniteIntegralAdeleLattice K L)

/-- The finite adelic class space `O(V)(K) \ O(V)(𝔸_f) / K_L`. -/
abbrev FiniteAdelicClassSpace
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  DoubleCoset.Quotient
    (RationalFiniteAdeleOrthogonalSubgroup K L :
      Set (RationalFiniteAdelicOrthogonalGroup K L))
    (RationalFiniteIntegralAdeleLatticeStabilizer K L :
      Set (RationalFiniteAdelicOrthogonalGroup K L))

end LeanCategories.Lattices.Valued
