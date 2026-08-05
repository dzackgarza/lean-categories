module

public import LeanCategories.Modules.Bilinear.Morphisms.Hom

@[expose] public section

namespace LeanCategories.Lattices.Integral

open LeanCategories.Modules.Bilinear

/-- Nondegeneracy: the adjoint map beta_B : L -> L* is injective. -/
def AdjointInjective (L : SymmBilinModuleCat ℤ) : Prop :=
  Function.Injective L.form

/-- Full subcategory IntegralLat ⊂ SymBil_Z.

There is deliberately no `Module ℤ carrier` field: an abelian group has exactly
one ℤ-module structure (`AddCommMonoid.subsingletonIntModule`), so such a field
is redundant. It is also actively harmful — an independent field is not
definitionally `AddCommGroup.toIntModule carrier`, so on a product carrier the
field-derived instance and Mathlib's `Prod.instModule` fail to agree and
constructions like `OrthogonalSum` cannot be built at all. -/
structure IntegralLattice where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [finite : Module.Finite ℤ carrier]
  [free : Module.Free ℤ carrier]
  form : LinearMap.BilinForm ℤ carrier
  isSymm : form.IsSymm
  nondegenerate : form.Nondegenerate

attribute [instance] IntegralLattice.addCommGroup
  IntegralLattice.finite IntegralLattice.free

/-- Automatic injectivity of form-preserving embeddings into nondegenerate lattices. -/
theorem embedding_injective {L M : IntegralLattice} (f : LeanCategories.Modules.Bilinear.Hom ⟨L.carrier, L.form, L.isSymm⟩ ⟨M.carrier, M.form, M.isSymm⟩) :
    Function.Injective f.toLinearMap := by
  intro x y hxy
  have h_diff : f.toLinearMap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h_form : ∀ z, L.form (x - y) z = 0 := by
    intro z
    have := f.map_form (x - y) z
    rw [h_diff, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  exact sub_eq_zero.mp (L.nondegenerate.1 (x - y) h_form)

/-- Subcategory EvenLat (2 | B(x,x)). -/
def IsEven (L : IntegralLattice) : Prop :=
  ∀ x, 2 ∣ L.form x x

end LeanCategories.Lattices.Integral
