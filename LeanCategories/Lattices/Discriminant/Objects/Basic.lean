module

public import LeanCategories.Lattices.Integral.Objects.Dual
public import LeanCategories.Lattices.Integral.Objects.EvenLat

@[expose] public section

namespace LeanCategories.Lattices.Discriminant

open LeanCategories.Lattices.Integral

/-- The additive circle ℚ/ℤ, represented by rational representatives modulo integral translation. -/
abbrev QModZ := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- The additive quotient ℚ/2ℤ used by finite quadratic forms. -/
abbrev QModTwoZ := ℚ ⧸ AddSubgroup.zmultiples (2 : ℚ)

/-- The canonical passage from bilinear values modulo ℤ to quadratic values modulo 2ℤ. -/
axiom bilinearValueInQuadraticQuotient : QModZ →+ QModTwoZ

/-- A finite abelian group equipped with a symmetric biadditive ℚ/ℤ-valued form. -/
structure FiniteBilinearModule where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [finite : Finite carrier]
  bilinForm : carrier →+ carrier →+ QModZ
  isSymm : ∀ x y, bilinForm x y = bilinForm y x

attribute [instance] FiniteBilinearModule.addCommGroup FiniteBilinearModule.finite

/-- A finite quadratic module with its polarization identity. -/
structure FiniteQuadraticModule extends FiniteBilinearModule where
  quadForm : carrier → QModTwoZ
  polarization : ∀ x y,
    quadForm (x + y) - quadForm x - quadForm y =
      bilinearValueInQuadraticQuotient (bilinForm x y)

/-- The discriminant group A_L = L*/L. -/
noncomputable def discrGroup (L : IntegralLattice) : Type _ := DiscriminantGroup L

instance (L : IntegralLattice) : AddCommGroup (discrGroup L) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- The induced discriminant bilinear form, defined by pairing dual lifts modulo ℤ. -/
axiom discrBilinearForm (L : IntegralLattice) :
    discrGroup L →+ discrGroup L →+ QModZ

axiom discrBilinearForm_symm (L : IntegralLattice) :
    ∀ x y, discrBilinearForm L x y = discrBilinearForm L y x

/-- The induced discriminant quadratic form of an even lattice. -/
axiom discrQuadraticForm (L : IntegralLattice) (hEven : IsEven L) :
    discrGroup L → QModTwoZ

axiom discrQuad_polarization (L : IntegralLattice) (hEven : IsEven L) :
    ∀ x y, discrQuadraticForm L hEven (x + y) - discrQuadraticForm L hEven x -
      discrQuadraticForm L hEven y =
        bilinearValueInQuadraticQuotient (discrBilinearForm L x y)

end LeanCategories.Lattices.Discriminant
