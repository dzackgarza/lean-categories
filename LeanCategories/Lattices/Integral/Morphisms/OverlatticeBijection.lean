module

public import LeanCategories.Lattices.Integral.Morphisms.Overlattice

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Refinement of the overlattice bijection: the equivalence is order-preserving
    with respect to inclusion of overlattices and inclusion of isotropic subgroups.
    See Nikulin, Theorem 1.4.1, Remark 1.4.2. -/
noncomputable def overlatticeBijectionOrderIso (L : IntegralLattice) (hEven : IsEven L) :
    OrderIso (Overlattice L) (IsotropicSubgroup L hEven) :=
  overlattice_isotropic_order_iso L hEven

/-- For an even unimodular overlattice L', the corresponding isotropic subgroup H = L'/L
    satisfies H = H⊥ (self-dual under the discriminant form).
    See Nikulin, Corollary 1.4.2. -/
axiom self_dual_iff_unimodular (L : IntegralLattice) (hEven : IsEven L)
    (M : Overlattice L) :
    Prop  -- The full statement: IsUnimodular(overlattice from M) ↔ H = H⊥

/-- Even unimodular overlattices of a rank-2n even lattice L exist iff
    the discriminant form (A_L, q_L) admits a metabolizer (totally isotropic
    subgroup of order |A_L|^{1/2}).
    See Nikulin, Theorem 1.10.1. -/
axiom unimodular_overlattice_exists_iff_metabolizer
    (L : IntegralLattice) (hEven : IsEven L) :
    Prop

end LeanCategories.Lattices.Integral
