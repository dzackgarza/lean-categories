/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildComplex
public import LeanCategories.Homological.TsyganBicomplex
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Relative cyclic homology of an ideal

Weibel, *An Introduction to Homological Algebra* (1994), §9.9,
pp. 358--359 (FC05-C09-U145).

For an ideal `I` in a `k`-algebra `R`, Weibel writes

`Z(R,I) = ker (Z(R) ⟶ Z(R/I))`

for the kernel cyclic module and defines

`HC_n(R,I) = HC_n(Z(R,I))`.

The realization below records the quotient map on pure Hochschild tensors and
the kernel universal property degreewise. The long exact sequence attached to
the short exact sequence of cyclic modules is result-level content and is not
asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped TensorProduct

universe u v

variable {C : Type u} [Category.{v} C]

/-- A morphism of cyclic objects: a simplicial morphism commuting with the
degreewise cyclic operators. -/
structure CyclicObjectHom (A B : CyclicObject (C := C)) where
  /-- The underlying simplicial morphism. -/
  hom : A.obj ⟶ B.obj
  /-- Compatibility with the cyclic operator in every degree. -/
  comm_t : ∀ n : ℕ,
    hom.app (op ⦋n⦌) ≫ (B.t n).hom =
      (A.t n).hom ≫ hom.app (op ⦋n⦌)

variable [Abelian C]

/-- A realization of the kernel of a morphism of cyclic objects. The kernel
property is required in every degree, while `obj` records the induced cyclic
structure on those kernels. -/
structure CyclicKernelRealization
    {A B : CyclicObject (C := C)} (f : CyclicObjectHom A B) where
  /-- The kernel cyclic object. -/
  obj : CyclicObject (C := C)
  /-- Inclusion into the source cyclic object. -/
  ι : CyclicObjectHom obj A
  /-- The composite with the quotient morphism vanishes degreewise. -/
  comp_zero : ∀ n : ℕ,
    ι.hom.app (op ⦋n⦌) ≫ f.hom.app (op ⦋n⦌) = 0
  /-- The inclusion has the kernel universal property in every degree. -/
  isKernel : ∀ n : ℕ,
    IsLimit (KernelFork.ofι (ι.hom.app (op ⦋n⦌)) (comp_zero n))

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]
variable (I : Ideal R) [I.IsTwoSided]
variable [Algebra k (R ⧸ I)]

/-- Source-faithful data for Weibel's kernel cyclic module `Z(R,I)`.

The two degree isomorphisms identify the source and target with the standard
Hochschild tensor models. `quotientMap_pure` requires the cyclic morphism to
be the tensorwise quotient map, so the chosen kernel is specifically
`ker(Z(R) → Z(R/I))`. -/
structure RelativeCyclicIdealRealization where
  /-- The cyclic module `Z(R)`. -/
  ZR : CyclicObject (C := ModuleCat.{max u v} k)
  /-- The cyclic module `Z(R/I)`. -/
  ZQuotient : CyclicObject (C := ModuleCat.{max u v} k)
  /-- Identification of `Z_n(R)` with the standard Hochschild tensor module. -/
  sourceDegreeIso : ∀ n : ℕ,
    ZR.obj.obj (op ⦋n⦌) ≅
      ModuleCat.of k (HochschildChainDegree (k := k) (R := R) (M := R) n)
  /-- Identification of `Z_n(R/I)` with the standard quotient tensor module. -/
  quotientDegreeIso : ∀ n : ℕ,
    ZQuotient.obj.obj (op ⦋n⦌) ≅
      ModuleCat.of k
        (HochschildChainDegree (k := k) (R := R ⧸ I) (M := R ⧸ I) n)
  /-- The quotient morphism `Z(R) ⟶ Z(R/I)`. -/
  quotientMap : CyclicObjectHom ZR ZQuotient
  /-- On pure tensors, the quotient morphism applies the ideal quotient map to
  every tensor factor. -/
  quotientMap_pure : ∀ (n : ℕ) (r₀ : R) (a : Fin n → R),
    (quotientDegreeIso n).hom
        (quotientMap.hom.app (op ⦋n⦌)
          ((sourceDegreeIso n).inv
            (hochschildChainPure (k := k) (R := R) (M := R) r₀ a))) =
      hochschildChainPure (k := k) (R := R ⧸ I) (M := R ⧸ I)
        (Ideal.Quotient.mk I r₀) (fun j => Ideal.Quotient.mk I (a j))
  /-- The kernel cyclic module `Z(R,I)`. -/
  kernel : CyclicKernelRealization quotientMap
  /-- Tsygan's bicomplex for the kernel cyclic module, used to define its
  cyclic homology. -/
  tsygan : TsyganBicomplexRealization kernel.obj

/-- Weibel's relative cyclic module `Z(R,I)`. -/
def relativeCyclicModule
    (D : RelativeCyclicIdealRealization k R I) :
    CyclicObject (C := ModuleCat.{max u v} k) :=
  D.kernel.obj

/-- Relative cyclic homology `HC_n(R,I) = HC_n(Z(R,I))`. -/
def relativeCyclicHomology
    (D : RelativeCyclicIdealRealization k R I)
    [HomologicalComplex₂.HasTotal D.tsygan.bicomplex (ComplexShape.down ℕ)]
    (n : ℕ) : ModuleCat.{max u v} k :=
  cyclicHomology D.kernel.obj D.tsygan n

end LeanCategories.Homological
