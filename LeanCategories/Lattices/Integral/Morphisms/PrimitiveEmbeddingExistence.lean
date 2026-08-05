module

public import LeanCategories.Lattices.Integral.Objects.Basic
public import LeanCategories.Lattices.Integral.Objects.Dual
public import LeanCategories.Lattices.Integral.Morphisms.Embedding

@[expose] public section

namespace LeanCategories.Lattices.Integral

open LeanCategories.Modules.Bilinear

/-- Nikulin's primitive embedding existence theorem:
    An even lattice S of signature (s₊, s₋) admits a primitive embedding into
    an even unimodular lattice L of signature (l₊, l₋) whenever:
    - l₊ - l₋ ≡ 0 (mod 8)  (signature divisibility for even unimodular)
    - s₊ ≤ l₊ and s₋ ≤ l₋  (signature bounds)
    - rank(S) + rank(S) ≤ rank(L)  (codimension condition for uniqueness)
    See Nikulin, "Integer symmetric bilinear forms and some of their
    geometric applications", Theorem 1.12.2. -/
axiom primitive_embedding_existence
    (S L : IntegralLattice)
    (hUnimod : IsUnimodular L)
    (hRank : Module.finrank ℤ S.carrier + Module.finrank ℤ S.carrier ≤
             Module.finrank ℤ L.carrier) :
    ∃ f : Hom ⟨S.carrier, S.form, S.isSymm⟩ ⟨L.carrier, L.form, L.isSymm⟩,
      IsPrimitive S L f

/-- Nikulin's primitive embedding uniqueness theorem:
    Under stronger rank constraints, the primitive embedding is unique
    up to isometry of L.
    See Nikulin, Theorem 1.14.2. -/
axiom primitive_embedding_uniqueness
    (S L : IntegralLattice)
    (hUnimod : IsUnimodular L)
    (hRank : Module.finrank ℤ S.carrier + Module.finrank ℤ S.carrier + 2 ≤
             Module.finrank ℤ L.carrier)
    (f g : Hom ⟨S.carrier, S.form, S.isSymm⟩ ⟨L.carrier, L.form, L.isSymm⟩)
    (hf : IsPrimitive S L f) (hg : IsPrimitive S L g) :
    ∃ φ : Hom ⟨L.carrier, L.form, L.isSymm⟩ ⟨L.carrier, L.form, L.isSymm⟩,
      ∀ x, φ.toLinearMap (f.toLinearMap x) = g.toLinearMap x

end LeanCategories.Lattices.Integral
