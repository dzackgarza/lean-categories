/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BrauerGroup.RelativeBrauer
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Brauer-group source data

Serre, *Local Fields*, Chapter X (FC10-C10-U027).

The pinned `BrauerGroup` package already owns the quotient of central simple
algebras, its tensor-product commutative group structure, and scalar extension.
This module imports that owner and records source-level names for the carrier
and base-change homomorphism.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

/-- Serre's Brauer group of a field (FC10-C10-U027).

The imported package's `CommGroup` instance is induced by tensor product of
central simple algebras. -/
abbrev serreBrauerGroup (K : Type u) [Field K] :=
  BrauerGroup K

/-- Scalar extension on Brauer groups (FC10-C10-U027). -/
noncomputable abbrev serreBrauerBaseChange
    (K E : Type u) [Field K] [Field E] [Algebra K E] :
    serreBrauerGroup K →* serreBrauerGroup E :=
  BrauerGroupHom.BaseChange

/-- Dummit--Foote's relative Brauer-group carrier, the kernel of scalar extension
(FC01-C17-U085). The splitting criterion remains theorem content. -/
abbrev relativeBrauerGroup (K F : Type u) [Field K] [Field F] [Algebra F K] :=
  RelativeBrGroup K F

/-- A field extension splits a central simple algebra when scalar extension is
isomorphic to a full matrix algebra (Dummit--Foote FC01-C17-U081). -/
abbrev SplitsCentralSimpleAlgebra
    (F K : Type u) [Field F] [Field K] [Algebra F K] (A : CSA F) : Prop :=
  isSplit F A K

/-- Brauer equivalence of central simple algebras, i.e. stable matrix
equivalence (Dummit--Foote FC01-C17-U083). -/
abbrev AreBrauerEquivalent
    (K : Type u) [Field K] (A B : CSA K) : Prop :=
  IsBrauerEquivalent A B

/-- Matrix/division-algebra data for the Wedderburn division-ring part of a
central simple algebra. -/
structure DivisionPartData
    (F : Type u) [Field F] (A : Type u) [Ring A] [Algebra F A] where
  n : ℕ
  hn : n ≠ 0
  divisionRing : Type u
  instDivisionRing : DivisionRing divisionRing
  instAlgebra : Algebra F divisionRing
  matrixEquiv : A ≃ₐ[F] Matrix (Fin n) (Fin n) divisionRing

attribute [instance] DivisionPartData.instDivisionRing
  DivisionPartData.instAlgebra

/-- The proved Artin--Wedderburn theorem supplies complete division-part data
for every central simple algebra. -/
theorem nonemptyDivisionPartData (F : Type u) [Field F] (A : CSA F) :
    Nonempty (DivisionPartData F A) := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite F A
  obtain ⟨n, hn, D, hD, hAlg, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing F A
  exact ⟨
    { n := n
      hn := hn.out
      divisionRing := D
      instDivisionRing := hD
      instAlgebra := hAlg
      matrixEquiv := e }⟩

/-- Construct the Wedderburn division-ring part of a central simple algebra
using Mathlib's proved Artin--Wedderburn decomposition
(Dummit--Foote FC01-C17-U082). -/
noncomputable def divisionPartData (F : Type u) [Field F] (A : CSA F) :
    DivisionPartData F A :=
  Classical.choice (nonemptyDivisionPartData F A)

end LeanCategories.Algebra
