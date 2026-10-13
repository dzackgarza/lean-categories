/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantQuadratic
public import LeanCategories.Lattices.Valued.Signature
public import LeanCategories.Lattices.Valued.Standard

/-!
# Index modulo eight of a quadratic torsion form

Peters--Sterk define the index modulo eight `τ₈(q)` of a nondegenerate finite quadratic
torsion form to be the signed index modulo eight of any nondegenerate even integral lattice
realizing `q` as its discriminant quadratic form (`FC11-C01-U131`, `FC11-C12-U001`, and
`FC11-C12-U006`).

Sweep III constructs the subtype of all realizing lattices and the resulting family of signed
indices modulo eight. The later realization theorem proves that this carrier is inhabited, and
the later independence theorem proves that its index family is a singleton. Neither theorem is
asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

local instance (priority := 10000) moduleIntFractionRing : Module ℤ (FractionRing ℤ) :=
  Algebra.toModule

local instance (priority := 10000) moduleIntDoubleFractionValueQuotient :
    Module ℤ (DoubleFractionValueQuotient ℤ) :=
  Submodule.Quotient.module (doubleAlgebraMap ℤ).range

/-- A finite projective integral lattice realizes `q` when it is nondegenerate and even and its
quadratic discriminant form is isometric to `q`. -/
def RealizesQuadraticTorsionForm
    (q : NonsingularFiniteTorsionQuadModuleCat ℤ (DoubleFractionValueQuotient ℤ))
    (L : FiniteProjectiveLatticeCat ℤ ℤ) : Prop := by
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  let qFinite : FiniteTorsionQuadModuleCat ℤ (DoubleFractionValueQuotient ℤ) :=
    ⟨q.obj, ⟨q.property.1, q.property.2.1⟩⟩
  exact ∃ (hL : IsFractionFieldPerfect ℤ L.obj) (hEven : IsEven L.obj),
    Nonempty (evenDiscriminantQuadraticFormModuleInt L.obj hL hEven ≅ qFinite)

/-- The carrier of all finite projective even integral lattices realizing `q`.
This is the source choice space itself; no unwitnessed realization is selected. -/
def QuadraticTorsionRealizationData
    (q : NonsingularFiniteTorsionQuadModuleCat ℤ (DoubleFractionValueQuotient ℤ)) :=
  {L : FiniteProjectiveLatticeCat ℤ ℤ // RealizesQuadraticTorsionForm q L}

/-- The signed index modulo eight attached to one valid realizing lattice. -/
def torsionIndexModEightOfRealization
    {q : NonsingularFiniteTorsionQuadModuleCat ℤ (DoubleFractionValueQuotient ℤ)}
    (L : QuadraticTorsionRealizationData q) : ZMod 8 :=
  (((integralSignature L.1).1 : ℤ) : ZMod 8) -
    (((integralSignature L.1).2.1 : ℤ) : ZMod 8)

/-- The Peters--Sterk index family before the later realization-independence theorem identifies
it with a single element of `ZMod 8`. -/
def torsionIndexModEightData
    (q : NonsingularFiniteTorsionQuadModuleCat ℤ (DoubleFractionValueQuotient ℤ)) : Set (ZMod 8) :=
  Set.range (torsionIndexModEightOfRealization (q := q))

end LeanCategories.Lattices.Valued
