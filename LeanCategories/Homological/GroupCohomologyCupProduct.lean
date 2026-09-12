/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.GroupCohomologyCrossProduct
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Cup product in group cohomology

Weibel, *An Introduction to Homological Algebra* (1994), §6.7, pp. 189--194
(FC05-C06-U090).

The cup product is the cohomological cross product followed by restriction along
the diagonal homomorphism `G → G × G`.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open scoped TensorProduct

variable (G : Type) [Group G]

/-- The diagonal homomorphism `g ↦ (g,g)`. -/
def groupDiagonal : G →* G × G where
  toFun g := (g, g)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical morphism from the restriction of the trivial `(G×G)`-module
along the diagonal to the trivial `G`-module. -/
noncomputable def diagonalTrivialHom :
    Rep.res (groupDiagonal G) (Rep.trivial ℤ (G × G) ℤ) ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ⟨LinearMap.id, fun g => by
    show LinearMap.id ∘ₗ LinearMap.id = LinearMap.id ∘ₗ LinearMap.id
    rfl⟩

/-- Restriction in group cohomology along the diagonal `G → G×G`. -/
noncomputable def groupCohomologyDiagonalMap (n : ℕ) :
    groupCohomology (Rep.trivial ℤ (G × G) ℤ) n ⟶
      groupCohomology (Rep.trivial ℤ G ℤ) n :=
  groupCohomology.map (groupDiagonal G) (diagonalTrivialHom G) n

/-- Weibel's cup product `x ∪ y = Δ*(x × y)`. -/
noncomputable def groupCohomologyCupProduct
    (X : GroupCohomologyCrossProduct G G) (p q : ℕ) :
    TensorProduct ℤ
        (groupCohomology (Rep.trivial ℤ G ℤ) p)
        (groupCohomology (Rep.trivial ℤ G ℤ) q) →ₗ[ℤ]
      groupCohomology (Rep.trivial ℤ G ℤ) (p + q) :=
  (groupCohomologyDiagonalMap G (p + q)).hom.comp (X.map p q)

end LeanCategories.Homological
