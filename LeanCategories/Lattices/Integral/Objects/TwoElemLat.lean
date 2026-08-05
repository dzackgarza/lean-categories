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

/-- Nikulin's classification theorem for 2-elementary even lattices:
    two such lattices with the same signature and (r,a,δ) invariants are isometric.
    See Nikulin, Theorem 3.6.2. -/
axiom nikulin_two_elementary_classification
    (L₁ L₂ : IntegralLattice)
    (hE₁ : IsEven L₁) (hE₂ : IsEven L₂)
    (h2₁ : IsTwoElementary L₁) (h2₂ : IsTwoElementary L₂)
    (hInv : nikulinInvariants L₁ hE₁ h2₁ = nikulinInvariants L₂ hE₂ h2₂) :
    Nonempty (L₁.carrier ≃ₗ[ℤ] L₂.carrier)

/-- Existence constraints on Nikulin invariants: a 2-elementary even lattice
    of signature (l₊, l₋) with invariants (r,a,δ) exists iff certain
    congruence conditions hold. See Nikulin, Theorem 3.6.2. -/
axiom nikulin_existence_constraints (inv : NikulinInvariants) (l_pos l_neg : ℕ) :
    Prop

end LeanCategories.Lattices.Integral
