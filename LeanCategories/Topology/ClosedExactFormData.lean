/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Closed and exact differential-form predicates

Definition-level realization of Lee FC08-C14-U038.

Lee's definitions of closedness and exactness use only the exterior-derivative
function itself.  They do not require the existence/uniqueness theorem that
constructs the global manifold exterior derivative, nor any of its linearity,
Leibniz, square-zero, or naturality properties.

Sweep III therefore records the predicates relative to a supplied differential
map.  FC08-C14-U035 remains the result-layer owner that supplies Lee's actual
global exterior derivative on smooth manifold forms.
-/

@[expose] public section

namespace LeanCategories.Topology

/-- A form is closed when its supplied exterior derivative is zero. -/
def IsClosedForm
    {Form NextForm : Type*} [Zero NextForm]
    (exteriorDerivative : Form → NextForm)
    (ω : Form) : Prop :=
  exteriorDerivative ω = 0

/-- A form is exact when it lies in the image of the supplied exterior
derivative from the preceding degree. -/
def IsExactForm
    {PrevForm Form : Type*}
    (exteriorDerivative : PrevForm → Form)
    (ω : Form) : Prop :=
  ∃ η : PrevForm, exteriorDerivative η = ω

end LeanCategories.Topology
