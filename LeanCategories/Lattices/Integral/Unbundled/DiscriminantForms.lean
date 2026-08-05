module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.DualAndDiscriminant
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Discriminant Forms, Overlattices, and Primitive Embeddings

This module formalizes:
- Discriminant group $A_L = L^\vee / L$
- Discriminant bilinear form $b_L : A_L \times A_L \to \mathbb{Q}/\mathbb{Z}$
- Discriminant quadratic form $q_L : A_L \to \mathbb{Q}/2\mathbb{Z}$ for even lattices
- Primitive submodules and primitive embeddings $S \hookrightarrow L$
- 2-elementary lattices and Nikulin invariants $(r, a, \delta)$
-/

namespace IntegralLattice

variable {L : Type*} [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L] [Module.Free ℤ L]

/-- A submodule $S \subseteq L$ is primitive if the quotient $L/S$ is torsion-free. -/
def IsPrimitiveSubmodule (S : Submodule ℤ L) : Prop :=
  Module.IsTorsionFree ℤ (L ⧸ S)

/-- A primitive embedding of lattices $M_1 \hookrightarrow M_2$. -/
structure PrimitiveEmbedding {L1 L2 : Type*}
    [AddCommGroup L1] [Module ℤ L1] [Module.Finite ℤ L1] [Module.Free ℤ L1]
    [AddCommGroup L2] [Module ℤ L2] [Module.Finite ℤ L2] [Module.Free ℤ L2]
    (M1 : IntegralLattice L1) (M2 : IntegralLattice L2) where
  toEmbedding : L1 →ₗ[ℤ] L2
  isInjective : Function.Injective toEmbedding
  isPrimitive : IsPrimitiveSubmodule (Submodule.map toEmbedding ⊤)
  isIsometry : ∀ x y, M2.eval (toEmbedding x) (toEmbedding y) = M1.eval x y

/-- A lattice is 2-elementary if its discriminant group is an elementary 2-group. -/
def IsTwoElementary (M : IntegralLattice L) : Prop :=
  ∀ f : L →ₗ[ℤ] ℤ, 2 • f ∈ LinearMap.range M.B

/-- Nikulin coparity invariant $\delta \in \{0, 1\}$, meaningfully studied for 2-elementary
lattices (`IsTwoElementary`) but stated generally: the formula does not need that hypothesis. -/
def TwoElementaryCoparity (M : IntegralLattice L) : Prop :=
  ∀ f : L →ₗ[ℤ] ℤ, ∃ v : L, M.B v = 2 • f ∧ Even (M.quad v / 2)


end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled
