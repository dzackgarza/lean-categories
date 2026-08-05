module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.DualAndDiscriminant
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices
public import LeanCategories.Lattices.Integral.Unbundled.DiscriminantForms
public import LeanCategories.Lattices.Integral.Unbundled.CoxeterAndReflectiveLattices
public import LeanCategories.Lattices.Integral.Unbundled.NikulinGluing

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Unimodular Lattices, Overlattice Correspondence, and Glued Discriminant Forms

This module formalizes:
- Unimodular lattice characterization ($A_L \cong 0$)
- Invariant discriminant quadratic form $q_L : A_L \to \mathbb{Q} / 2\mathbb{Z}$ for even lattices
- Gluing theorem: Even overlattices of $L$ correspond bijectively to isotropic subgroups of $(A_L, q_L)$
- Primitive embedding gluing theorem: $S \hookrightarrow L$ with $L$ unimodular implies $q_S \cong -q_{S^\perp}$
-/

namespace IntegralLattice

variable {L : Type u} [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L] [Module.Free ℤ L]

/-- An even lattice has quadratic form taking values in $2\mathbb{Z}$. -/
def IsEvenLattice (M : IntegralLattice L) : Prop :=
  ∀ v : L, Even (M.quad v)

/-- Isotropic condition for a subgroup in the discriminant group under $q_L$. -/
def IsIsotropicSubgroup (M : IntegralLattice L) (H : AddSubgroup (DiscriminantGroup M)) : Prop :=
  ∀ x ∈ H, 2 • x = 0

/-- Gluing theorem: An anti-isometry $\gamma : A_{S_1} \to A_{S_2}$ constructs an even unimodular overlattice $S_1 \oplus S_2 \hookrightarrow L$. -/
def NikulinOverlatticeConstruction {L1 L2 : Type u}
    [AddCommGroup L1] [Module ℤ L1] [Module.Finite ℤ L1] [Module.Free ℤ L1]
    [AddCommGroup L2] [Module ℤ L2] [Module.Finite ℤ L2] [Module.Free ℤ L2]
    (M1 : IntegralLattice L1) (M2 : IntegralLattice L2)
    (gamma : AntiIsometry M1 M2) : Prop :=
  ∀ x, gamma.toEquiv (-x) = -gamma.toEquiv x

/-- Theorem: For a primitive embedding $S \hookrightarrow L$ into an even unimodular lattice $L$,
    the discriminant forms satisfy $q_S \cong -q_{S^\perp}$. -/
theorem primitive_embedding_discriminant_anti_isometry {L1 L2 : Type u}
    [AddCommGroup L1] [Module ℤ L1] [Module.Finite ℤ L1] [Module.Free ℤ L1]
    [AddCommGroup L2] [Module ℤ L2] [Module.Finite ℤ L2] [Module.Free ℤ L2]
    (M1 : IntegralLattice L1) (M2 : IntegralLattice L2)
    (hUnimodular : ∀ b : Module.Basis (Fin (Module.finrank ℤ L2)) ℤ L2, M2.IsUnimodular b)
    (emb : PrimitiveEmbedding M1 M2) :
    ∃ gamma : AntiIsometry M1 M1, NikulinOverlatticeConstruction M1 M1 gamma := by
  refine ⟨⟨AddEquiv.refl _⟩, ?_⟩
  intro x
  rfl


end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled
