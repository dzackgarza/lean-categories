/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.NoncommutativeTensor

/-!
# Morita contexts by bimodules

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.5.1,
§9.5, pp. 326--329 (FC05-C09-U073).

Weibel calls rings `R` and `S` Morita equivalent when there are bimodules
`_R P_S` and `_S Q_R` for which

`P ⊗_S Q ≅ R` and `Q ⊗_R P ≅ S`

as bimodules. The relative tensor products below are the project's genuine
noncommutative tensor products. Rather than replace this source definition by
the equivalent categorical definition in Mathlib, we record the two
bimodules and the two additive equivalences together with their left- and
right-linearity on pure tensors. Since pure tensors generate each relative
tensor product, these are exactly the bimodule-equivariance conditions.
-/

@[expose] public section

namespace LeanCategories.Homological

open scoped TensorProduct

universe u

/-- The class of a pure tensor `a ⊗_R b` in the noncommutative relative
tensor product. -/
def relativeTensorPure (R : Type u) [Ring R]
    (A : ModuleCat Rᵐᵒᵖ) (B : ModuleCat R) (a : A) (b : B) :
    RelativeTensor R A B :=
  Submodule.Quotient.mk (a ⊗ₜ[ℤ] b)

/-- Weibel's explicit Morita-equivalence data: bimodules `_R P_S` and
`_S Q_R` with `P ⊗_S Q ≅ R` and `Q ⊗_R P ≅ S` as bimodules.

Source: Weibel, Definition 9.5.1 (FC05-C09-U073). -/
structure WeibelMoritaContext (R S : Type u) [Ring R] [Ring S] where
  /-- The `(R,S)`-bimodule `P`. -/
  P : Type u
  /-- The `(S,R)`-bimodule `Q`. -/
  Q : Type u
  [PAdd : AddCommGroup P]
  [QAdd : AddCommGroup Q]
  [PLeftR : Module R P]
  [PRightS : Module Sᵐᵒᵖ P]
  [QLeftS : Module S Q]
  [QRightR : Module Rᵐᵒᵖ Q]
  [PComm : SMulCommClass R Sᵐᵒᵖ P]
  [QComm : SMulCommClass S Rᵐᵒᵖ Q]
  /-- The additive equivalence underlying `P ⊗_S Q ≅ R`. -/
  pTensorQ :
    RelativeTensor S (ModuleCat.of Sᵐᵒᵖ P) (ModuleCat.of S Q) ≃+ R
  /-- Left `R`-linearity of `P ⊗_S Q ≅ R` on pure tensors. -/
  pTensorQ_left (r : R) (p : P) (q : Q) :
    pTensorQ
        (relativeTensorPure S (ModuleCat.of Sᵐᵒᵖ P) (ModuleCat.of S Q)
          (r • p) q) =
      r * pTensorQ
        (relativeTensorPure S (ModuleCat.of Sᵐᵒᵖ P) (ModuleCat.of S Q) p q)
  /-- Right `R`-linearity of `P ⊗_S Q ≅ R` on pure tensors. -/
  pTensorQ_right (r : R) (p : P) (q : Q) :
    pTensorQ
        (relativeTensorPure S (ModuleCat.of Sᵐᵒᵖ P) (ModuleCat.of S Q)
          p ((MulOpposite.op r : Rᵐᵒᵖ) • q)) =
      pTensorQ
          (relativeTensorPure S (ModuleCat.of Sᵐᵒᵖ P) (ModuleCat.of S Q) p q) * r
  /-- The additive equivalence underlying `Q ⊗_R P ≅ S`. -/
  qTensorP :
    RelativeTensor R (ModuleCat.of Rᵐᵒᵖ Q) (ModuleCat.of R P) ≃+ S
  /-- Left `S`-linearity of `Q ⊗_R P ≅ S` on pure tensors. -/
  qTensorP_left (s : S) (q : Q) (p : P) :
    qTensorP
        (relativeTensorPure R (ModuleCat.of Rᵐᵒᵖ Q) (ModuleCat.of R P)
          (s • q) p) =
      s * qTensorP
        (relativeTensorPure R (ModuleCat.of Rᵐᵒᵖ Q) (ModuleCat.of R P) q p)
  /-- Right `S`-linearity of `Q ⊗_R P ≅ S` on pure tensors. -/
  qTensorP_right (s : S) (q : Q) (p : P) :
    qTensorP
        (relativeTensorPure R (ModuleCat.of Rᵐᵒᵖ Q) (ModuleCat.of R P)
          q ((MulOpposite.op s : Sᵐᵒᵖ) • p)) =
      qTensorP
          (relativeTensorPure R (ModuleCat.of Rᵐᵒᵖ Q) (ModuleCat.of R P) q p) * s

/-- Weibel's Definition 9.5.1 as a proposition on two rings. -/
def AreMoritaEquivalentByBimodules (R S : Type u) [Ring R] [Ring S] : Prop :=
  Nonempty (WeibelMoritaContext R S)

end LeanCategories.Homological
