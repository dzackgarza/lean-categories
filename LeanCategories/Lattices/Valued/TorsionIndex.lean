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

The realizing lattice is selected by `Classical.epsilon`. The later realization theorem is
needed to prove that this selected lattice satisfies `RealizesQuadraticTorsionForm`; the later
independence theorem is needed to identify `torsionIndexModEight q` with the index of any supplied
realization. Neither theorem is asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

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

/-- A classically chosen finite projective integral lattice intended to realize `q`.

The ambient lattice type is nonempty by the rank-zero lattice. Theorem 12.1.1 is the separate
statement that the realization predicate is inhabited, and will imply that this epsilon choice
actually realizes `q`. -/
def chosenQuadraticTorsionRealization
    (q : NonsingularFiniteTorsionQuadModuleCat ℤ (DoubleFractionValueQuotient ℤ)) :
    FiniteProjectiveLatticeCat ℤ ℤ := by
  letI : Nonempty (FiniteProjectiveLatticeCat ℤ ℤ) := ⟨rankZeroFiniteLattice⟩
  exact Classical.epsilon (RealizesQuadraticTorsionForm q)

/-- The Peters--Sterk index modulo eight `τ₈(q)`: the positive index minus the negative
index of the chosen realizing lattice, reduced in `ZMod 8`. -/
def torsionIndexModEight
    (q : NonsingularFiniteTorsionQuadModuleCat ℤ (DoubleFractionValueQuotient ℤ)) : ZMod 8 :=
  (((integralSignature (chosenQuadraticTorsionRealization q)).1 : ℤ) : ZMod 8) -
    (((integralSignature (chosenQuadraticTorsionRealization q)).2.1 : ℤ) : ZMod 8)

end LeanCategories.Lattices.Valued
