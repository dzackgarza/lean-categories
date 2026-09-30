/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

@[expose] public section

/-!
# The kernel of a group homomorphism is an equalizer

For `f : G ⟶ H` in `Grp`, the subgroup `ker f` with its inclusion is an equalizer of `f` and the
trivial homomorphism `1`. `Grp` is not preadditive, so this is the kernel as an equalizer, stated
as Mathlib states `AddCommGrpCat.kernelIsLimit` (`Mathlib/Algebra/Category/Grp/Kernels.lean`) for
abelian groups.
-/

open CategoryTheory Limits

namespace LeanCategories.Algebra

universe u

variable {G H : GrpCat.{u}} (f : G ⟶ H)

/-- The fork of `f` and the trivial homomorphism on `ker f`. -/
def kernelFork : Fork f 1 :=
  Fork.ofι (P := GrpCat.of f.hom.ker) (GrpCat.ofHom f.hom.ker.subtype) <| by
    ext x
    exact x.2

/-- `ker f` with its inclusion is an equalizer of `f` and `1`. -/
def kernelForkIsLimit : IsLimit (kernelFork f) :=
  Fork.IsLimit.mk _
    (fun s => GrpCat.ofHom <| s.ι.hom.codRestrict _ fun c =>
      MonoidHom.mem_ker.mpr (ConcreteCategory.congr_hom s.condition c))
    (fun _ => rfl)
    (fun _ _ h => GrpCat.ext fun x => Subtype.ext (ConcreteCategory.congr_hom h x))

/-- The kernel of `f`, as a limit cone of the parallel pair `(f, 1)`. -/
def kernelLimitCone : LimitCone (parallelPair f 1) := ⟨kernelFork f, kernelForkIsLimit f⟩

end LeanCategories.Algebra
