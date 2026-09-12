/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.TripleCohomology
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# André--Quillen homology and cohomology

Weibel, *An Introduction to Homological Algebra* (1994), Definitions 8.8.2,
§8.8, pp. 294--299 (FC05-C08-U098).

Given an augmented simplicial commutative `k`-algebra `P_* → R`, the
cotangent complex has degree
`R ⊗_{P_n} Ω_{P_n/k}`, while the cohomological construction has degree
`Der_k(P_n,M)`.  This file records those literal degree objects, packages
realizations by a chain and cosimplicial object, and defines André--Quillen
(co)homology from them.

For the canonical free-algebra cotriple resolution, existence of these
realizations and comparison with arbitrary simplicial polynomial resolutions
belong to the theorem layer.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial
open scoped TensorProduct

universe u

variable (k : Type u) [CommRing k]
variable (P : SimplicialObject.Augmented (CommAlgCat k))

/-- The augmentation `P_n → R` in degree `n`, where `R` is the point of the
augmented simplicial algebra. -/
def aqAugmentation (n : ℕ) :
    (P.left.obj (op ⦋n⦌) : Type u) →ₐ[k] (P.right : Type u) :=
  (P.hom.app (op ⦋n⦌)).hom

/-- Degree `n` of the cotangent complex:
`R ⊗_{P_n} Ω_{P_n/k}`. -/
def aqCotangentDegree (n : ℕ) : ModuleCat (P.right : Type u) := by
  letI : Algebra (P.left.obj (op ⦋n⦌) : Type u) (P.right : Type u) :=
    (aqAugmentation k P n).toRingHom.toAlgebra
  exact ModuleCat.of (P.right : Type u)
    ((P.right : Type u) ⊗[(P.left.obj (op ⦋n⦌) : Type u)]
      KaehlerDifferential k (P.left.obj (op ⦋n⦌) : Type u))

variable (M : Type u) [AddCommGroup M] [Module (P.right : Type u) M]
  [Module k M] [IsScalarTower k (P.right : Type u) M]

/-- Degree `n` of the André--Quillen derivation cosimplicial module:
`Der_k(P_n,M)`, with `P_n` acting on `M` through the augmentation `P_n → R`. -/
def aqDerivationDegree (n : ℕ) : ModuleCat (P.right : Type u) := by
  letI : Module (P.left.obj (op ⦋n⦌) : Type u) M :=
    Module.compHom M (aqAugmentation k P n).toRingHom
  letI : SMulCommClass (P.right : Type u) (P.left.obj (op ⦋n⦌) : Type u) M :=
    ⟨fun r p m => by
      change r • ((aqAugmentation k P n) p • m) =
        (aqAugmentation k P n) p • (r • m)
      exact smul_comm r ((aqAugmentation k P n) p) m⟩
  exact ModuleCat.of (P.right : Type u)
    (Derivation k (P.left.obj (op ⦋n⦌) : Type u) M)

/-- A realization of Weibel's André--Quillen constructions for an augmented
simplicial algebra `P_* → R` and coefficient module `M`.

The two isomorphism families state exactly the degree formulas from Definition
8.8.2.  The differentials/cofaces are those of the supplied chain and
cosimplicial objects. -/
structure AndreQuillenRealization where
  /-- The cotangent chain complex `L_{R/k}`. -/
  cotangentComplex : ChainComplex (ModuleCat (P.right : Type u)) ℕ
  /-- Its degree-`n` term is `R ⊗_{P_n} Ω_{P_n/k}`. -/
  cotangentDegreeIso : ∀ n : ℕ,
    cotangentComplex.X n ≅ aqCotangentDegree k P n
  /-- The cosimplicial derivation module. -/
  derivationCosimplicial : CosimplicialObject (ModuleCat (P.right : Type u))
  /-- Its degree-`n` term is `Der_k(P_n,M)`. -/
  derivationDegreeIso : ∀ n : ℕ,
    derivationCosimplicial.obj ⦋n⦌ ≅ aqDerivationDegree k P M n

/-- Weibel's cotangent complex `L_{R/k}` associated to the chosen simplicial
resolution realization. -/
def andreQuillenCotangentComplex (Q : AndreQuillenRealization k P M) :
    ChainComplex (ModuleCat (P.right : Type u)) ℕ :=
  Q.cotangentComplex

/-- Weibel's André--Quillen cohomology
`D^n(R/k,M)=π^n Der_k(P_*,M)`. -/
def andreQuillenCohomology (Q : AndreQuillenRealization k P M) (n : ℕ) :
    ModuleCat (P.right : Type u) :=
  cosimplicialCohomotopyObject (ModuleCat (P.right : Type u))
    Q.derivationCosimplicial n

/-- Tensor the cotangent complex with the coefficient module `M`. -/
def andreQuillenTensorComplex (Q : AndreQuillenRealization k P M) :
    ChainComplex (ModuleCat (P.right : Type u)) ℕ :=
  (((MonoidalCategory.tensorLeft (ModuleCat.of (P.right : Type u) M)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj Q.cotangentComplex)

/-- Weibel's André--Quillen homology
`D_n(R/k,M)=H_n(M ⊗_R L_{R/k})`. -/
def andreQuillenHomology (Q : AndreQuillenRealization k P M) (n : ℕ) :
    ModuleCat (P.right : Type u) :=
  (HomologicalComplex.homologyFunctor (ModuleCat (P.right : Type u))
    (ComplexShape.down ℕ) n).obj (andreQuillenTensorComplex k P M Q)

end LeanCategories.Homological
