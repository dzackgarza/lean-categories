module

public import LeanCategories.Lattices.Discriminant.Objects.Basic
public import LeanCategories.Lattices.Integral.Morphisms.Embedding

@[expose] public section

namespace LeanCategories.Lattices.Discriminant

open LeanCategories.Lattices.Integral

/-- An anti-isometry between finite quadratic modules: an isomorphism
    γ : (A₁, q₁) ≅ (A₂, -q₂) such that q₂(γ(x)) = -q₁(x).
    These arise from primitive embeddings S ↪ L via the identification
    γ : (A_S, q_S) ≅ (A_{S⊥}, -q_{S⊥}). -/
structure AntiIsometry (A₁ A₂ : FiniteQuadraticModule) where
  equiv : A₁.carrier ≃+ A₂.carrier
  anti_preserves : ∀ x, A₂.quadForm (equiv x) = -A₁.quadForm x

/-- A primitive isometric embedding of integral lattices. -/
structure PrimitiveEmbedding (S L : IntegralLattice) where
  hom : LeanCategories.Modules.Bilinear.Hom
    ⟨S.carrier, S.form, S.isSymm⟩ ⟨L.carrier, L.form, L.isSymm⟩
  primitive : IsPrimitive S L hom

/-- Discriminant gluing datum attached to a primitive embedding. -/
structure PrimitiveEmbeddingDiscriminantData (S L : IntegralLattice) where
  complementModule : FiniteQuadraticModule
  sourceModule : FiniteQuadraticModule
  sourceCarrier : sourceModule.carrier = discrGroup S
  antiIsometry : AntiIsometry sourceModule complementModule

end LeanCategories.Lattices.Discriminant
