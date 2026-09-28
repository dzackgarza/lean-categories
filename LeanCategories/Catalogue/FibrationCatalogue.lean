/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Syntax
public import LeanCategories.Modules.Expressions
public import LeanCategories.Algebra.Catalogue.Rings

@[expose] public section

/-!
# Stable identities and expressions of the registered fibrations (CC-FIB)

* `fib.modules`: the cartesian fibration `∫ᶜ Mod → Ring` of restriction of scalars.
* `fib.modules_ext`: the cocartesian fibration `∫ Mod → CommRing` of extension of scalars.
* `fib.bilin_forms`: the cocartesian fibration `p : Bil → ∫ Mod` of bilinear forms over
  modules over rings (FOUNDATIONS Example 31.2c), whose composite with `fib.modules_ext` is
  the projection of forms to rings.
-/

namespace LeanCategories

namespace CategoryId
/-- `∫ Mod` over commutative rings, with extension of scalars. -/
def modulesOverRingsExt : CategoryId := ⟨"cat.modules_over_rings_ext"⟩
/-- Bilinear forms over all commutative rings and value modules. -/
def bilinFormsOverRings : CategoryId := ⟨"cat.bilin_forms_over_rings"⟩
/-- Lattices: the refinement of `Bil` by the lattice property. -/
def latticesOverRings : CategoryId := ⟨"cat.lattices_over_rings"⟩
end CategoryId

namespace ClassifierId
/-- The lattice property on `Bil` (projective carrier, symmetric form). -/
def bilLattice : ClassifierId := ⟨"clf.bilin_forms.lattice"⟩
end ClassifierId

namespace FunctorId
/-- The projection `∫ᶜ Mod ⥤ Ring`. -/
def modulesProjection : FunctorId := ⟨"fun.modules.projection"⟩
/-- The projection `∫ Mod ⥤ CommRing` of the extension-of-scalars fibration. -/
def modulesExtRing : FunctorId := ⟨"fun.modules_ext.ring"⟩
/-- The projection `p : Bil ⥤ ∫ Mod` of forms to their value modules over their rings. -/
def bilinFormsValues : FunctorId := ⟨"fun.bilin_forms.values"⟩
end FunctorId

namespace FibrationId
def modules : FibrationId := ⟨"fib.modules"⟩
def modulesExt : FibrationId := ⟨"fib.modules_ext"⟩
def bilinForms : FibrationId := ⟨"fib.bilin_forms"⟩
end FibrationId

namespace Fibrations

def ModulesOverRingsExt : CategoryExpr := .atom CategoryId.modulesOverRingsExt
def BilinFormsOverRings : CategoryExpr := .atom CategoryId.bilinFormsOverRings

/-- Lattices, as the refinement of `Bil` by the lattice property (audit §4). -/
def LatticesOverRings : CategoryExpr := .refine BilinFormsOverRings ClassifierId.bilLattice

def ModulesProjectionExpr : FunctorExpr Modules.ModulesTotal Algebra.Catalogue.Rings.Rings :=
  .atomic FunctorId.modulesProjection
def ModulesExtRingExpr :
    FunctorExpr ModulesOverRingsExt Algebra.Catalogue.Rings.CommutativeRings :=
  .atomic FunctorId.modulesExtRing
def BilinFormsValuesExpr : FunctorExpr BilinFormsOverRings ModulesOverRingsExt :=
  .atomic FunctorId.bilinFormsValues

end Fibrations

end LeanCategories
