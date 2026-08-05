module

public import LeanCategories.Lattices.Integral.Objects.EvenLat
public import LeanCategories.Lattices.Integral.Objects.Dual

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Subcategory TwoElemLat: 2x = 0 on A_L (the discriminant group is 2-elementary). -/
def IsTwoElementary (L : IntegralLattice) : Prop :=
  ∀ x : DiscriminantGroup L, 2 • x = 0

/-- Nikulin invariants (r, a, δ) classifying 2-elementary even lattices.
    - r = rank of L
    - a = rank of the 2-elementary discriminant group (|A_L| = 2^a)
    - δ ∈ {0, 1}: δ = 0 iff q_L takes values in ℤ, δ = 1 iff q_L takes values in ½ℤ. -/
structure NikulinInvariants where
  r : ℕ
  a : ℕ
  delta : Fin 2
  ha_le_r : a ≤ r

/-- Compute the Nikulin invariants of a 2-elementary even lattice.
    See Nikulin, "Integer symmetric bilinear forms and some of their
    geometric applications", §3. -/
axiom nikulinInvariants (L : IntegralLattice) (hEven : IsEven L)
    (h2elem : IsTwoElementary L) : NikulinInvariants

end LeanCategories.Lattices.Integral
