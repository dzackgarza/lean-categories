/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Canonical low-degree Tate classes

Definition-level realization of Serre FC10-C11-U036.

Serre writes a bar over an invariant element to denote its canonical image in
Tate degree zero, and similarly writes the class of an element killed by the
norm in Tate degree minus one.

No quotient-comparison theorem is needed merely to name these classes.
Mathlib already identifies degree-zero group cocycles with invariant
coefficients, and its Tate complex has a native cycle object in every degree
with the canonical homology-class map

`(tateComplex A).homologyπ n : cycles n ⟶ homology n`.

Accordingly, the source hypotheses are represented exactly as Serre states
them: an element of the invariant submodule in degree zero, and an element of
the norm kernel in degree minus one. Existing kernel equations transport those
elements to Tate cycles, after which the native homology-class map gives the
canonical classes. The explicit quotient descriptions of the resulting Tate
groups are result/comparison statements and are not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory groupCohomology groupHomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Serre's degree-zero source datum: a coefficient fixed by G. -/
abbrev TateDegreeZeroInvariantData (A : Rep R G) :=
  A.ρ.invariants

/-- The Tate degree-zero cycle canonically determined by an invariant
coefficient. -/
def tateDegreeZeroCycleData (A : Rep R G)
    (a : TateDegreeZeroInvariantData A) :
    (tateComplex A).cycles (0 : ℤ) :=
  let z := (cocyclesIso₀ A).inv a
  HomologicalComplex.cyclesMk (tateComplex A)
    (iCocycles A 0 z) 1 (by simp) <| by
      change
        (inhomogeneousCochains A).d 0 1 (iCocycles A 0 z) = 0
      simpa [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom
          ((inhomogeneousCochains A).iCycles_d 0 1) z

/-- The underlying coefficient of Serre's invariant degree-zero datum, read
back through the Tate-cycle inclusion. -/
def tateDegreeZeroCycleValueData (A : Rep R G)
    (a : TateDegreeZeroInvariantData A) : A.V :=
  (cochainsIso₀ A).hom
    ((tateComplex A).iCycles 0 (tateDegreeZeroCycleData A a))

/-- Serre's barred degree-zero element: the canonical homology class of the
supplied invariant coefficient. -/
def tateDegreeZeroClassData (A : Rep R G)
    (a : TateDegreeZeroInvariantData A) :
    tateCohomology A 0 :=
  (tateComplex A).homologyπ 0 (tateDegreeZeroCycleData A a)

/-- Serre's degree-minus-one source datum: a coefficient killed by the norm. -/
abbrev TateDegreeNegOneNormKernelData (A : Rep R G) :=
  LinearMap.ker A.ρ.norm

/-- The Tate degree-minus-one cycle canonically determined by a coefficient in
the norm kernel. -/
def tateDegreeNegOneCycleData (A : Rep R G)
    (a : TateDegreeNegOneNormKernelData A) :
    (tateComplex A).cycles (-1 : ℤ) :=
  HomologicalComplex.cyclesMk (tateComplex A)
    ((chainsIso₀ A).inv a.1) 0 (by simp) <| by
      change A.tateNorm ((chainsIso₀ A).inv a.1) = 0
      simp [Rep.tateNorm]

/-- The underlying coefficient of Serre's norm-kernel datum, read back through
the Tate-cycle inclusion and the native degree-minus-one chain identification. -/
def tateDegreeNegOneCycleValueData (A : Rep R G)
    (a : TateDegreeNegOneNormKernelData A) : A.V :=
  (chainsIso₀ A).hom
    ((tateComplex A).iCycles (-1) (tateDegreeNegOneCycleData A a))

/-- Serre's barred degree-minus-one element: the canonical homology class of
the supplied norm-zero coefficient. -/
def tateDegreeNegOneClassData (A : Rep R G)
    (a : TateDegreeNegOneNormKernelData A) :
    tateCohomology A (-1) :=
  (tateComplex A).homologyπ (-1) (tateDegreeNegOneCycleData A a)

end LeanCategories.Homological
