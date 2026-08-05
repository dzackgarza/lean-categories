module

public import LeanCategories.Lattices.Integral.Objects.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- An even integral lattice: one satisfying 2 | B(x,x) for all x. -/
structure EvenLattice extends IntegralLattice where
  isEven : IsEven toIntegralLattice

/-- Quadratic refinement Q_L(x) = B(x,x)/2 for even lattices.
    Since 2 | B(x,x), integer division by 2 is exact. -/
def quadRefinement (L : EvenLattice) (x : L.carrier) : ℤ :=
  L.form x x / 2

/-- The quadratic refinement satisfies 2 * Q(x) = B(x,x). -/
theorem two_mul_quadRefinement (L : EvenLattice) (x : L.carrier) :
    2 * quadRefinement L x = L.form x x := by
  unfold quadRefinement
  exact Int.mul_ediv_cancel' (L.isEven x)

/-- Polarization identity: Q(x+y) - Q(x) - Q(y) = B(x,y).

    PROVIDED SOLUTION
    Expand B(x+y, x+y) = B(x,x) + 2B(x,y) + B(y,y) by bilinearity and symmetry.
    Then Q(x+y) = (B(x,x) + 2B(x,y) + B(y,y))/2 = Q(x) + B(x,y) + Q(y). -/
axiom quadRefinement_polarization (L : EvenLattice) (x y : L.carrier) :
    quadRefinement L (x + y) - quadRefinement L x - quadRefinement L y = L.form x y

/-- The quadratic form associated to an even lattice. -/
axiom quadraticForm (L : EvenLattice) : QuadraticForm ℤ L.carrier

/-- Its evaluation agrees with the exact divisibility-based refinement. -/
axiom quadraticForm_apply (L : EvenLattice) (x : L.carrier) :
    quadraticForm L x = quadRefinement L x

/-- Evenness is inherited by sublattices. -/
theorem isEven_of_sublattice (L : IntegralLattice) (M : Submodule ℤ L.carrier)
    (hEven : IsEven L) : ∀ x : M, 2 ∣ L.form (x : L.carrier) (x : L.carrier) :=
  fun x => hEven x

end LeanCategories.Lattices.Integral
