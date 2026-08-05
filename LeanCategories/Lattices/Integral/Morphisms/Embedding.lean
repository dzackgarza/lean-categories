module

public import LeanCategories.Lattices.Integral.Objects.Dual

@[expose] public section

namespace LeanCategories.Lattices.Integral

open LeanCategories.Modules.Bilinear

/-- A lattice morphism is primitive when its cokernel is torsion-free. -/
def IsPrimitive (L M : IntegralLattice)
    (f : Hom ⟨L.carrier, L.form, L.isSymm⟩ ⟨M.carrier, M.form, M.isSymm⟩) : Prop :=
  Module.IsTorsionFree ℤ (M.carrier ⧸ LinearMap.range f.toLinearMap)

/-- Pairing with the embedded lattice, viewed as a map to its dual. -/
axiom orthogonalPairingMap (L M : IntegralLattice)
    (f : Hom ⟨L.carrier, L.form, L.isSymm⟩ ⟨M.carrier, M.form, M.isSymm⟩) :
    M.carrier →ₗ[ℤ] Module.Dual ℤ L.carrier

/-- Orthogonal complement S⊥ inside the ambient lattice. -/
noncomputable def OrthogonalComplement (L M : IntegralLattice)
    (f : Hom ⟨L.carrier, L.form, L.isSymm⟩ ⟨M.carrier, M.form, M.isSymm⟩) :
    Submodule ℤ M.carrier :=
  LinearMap.ker (orthogonalPairingMap L M f)

/-- A primitive sublattice and its orthogonal complement have finite-index sum. -/
axiom primitive_orthogonal_sum_finite_index
    (L M : IntegralLattice)
    (f : Hom ⟨L.carrier, L.form, L.isSymm⟩ ⟨M.carrier, M.form, M.isSymm⟩)
    (hPrim : IsPrimitive L M f) :
    Finite (M.carrier ⧸ (LinearMap.range f.toLinearMap ⊔ OrthogonalComplement L M f))

/-- In a unimodular ambient lattice, the orthogonal complement is nondegenerate. -/
axiom orthogonal_complement_nondegenerate
    (L M : IntegralLattice)
    (f : Hom ⟨L.carrier, L.form, L.isSymm⟩ ⟨M.carrier, M.form, M.isSymm⟩)
    (hPrim : IsPrimitive L M f) (hUnimod : IsUnimodular M) :
    ∀ x : OrthogonalComplement L M f,
      (∀ y : OrthogonalComplement L M f,
        M.form (x : M.carrier) (y : M.carrier) = 0) → (x : M.carrier) = 0

end LeanCategories.Lattices.Integral
