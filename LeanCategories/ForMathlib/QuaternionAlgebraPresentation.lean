/-
Copyright (c) 2026 Daniel Zack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Zack Garza
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.QuaternionBasis

/-!
# Quaternion algebras by a symbol presentation

Peters--Sterk, *Symmetric and Quadratic Forms* (June 2024), Definition 5.4.1
(`FC11-C05-U052`), define a quaternion algebra over a field of characteristic different from
two by a central algebra admitting a quadratic-extension presentation `D = K + K j`, with
`K = k[i]`, `i², j² ∈ kˣ`, and `j (x + i y) = (x - i y) j`.

Mathlib's `QuaternionAlgebra k a 0 b` is the corresponding symbol algebra. Its canonical
`QuaternionAlgebra.Basis.self` has the required generators and relations, while
`QuaternionAlgebra.basisOneIJK` supplies the four-coordinate basis. The definition below says
that a supplied algebra has this presentation; it does not replace the presentation by the
abstract central-simple-rank-four characterization.
-/

@[expose] public section

namespace LeanCategories.ForMathlib

/-- A quaternion algebra in the sense of Peters--Sterk, Definition 5.4.1.

The units `a` and `b` are the source parameters `i²` and `j²`. The algebra equivalence
transports the canonical `1, i, j, ij` presentation of `QuaternionAlgebra k a 0 b` to `D`.
-/
class IsQuaternionAlgebra (k : Type*) [Field k] [NeZero (2 : k)]
    (D : Type*) [Ring D] [Algebra k D] : Prop where
  isCentral : Algebra.IsCentral k D
  presentation :
    ∃ a b : kˣ, Nonempty (D ≃ₐ[k] QuaternionAlgebra k (a : k) 0 (b : k))

namespace IsQuaternionAlgebra

attribute [instance] isCentral

end IsQuaternionAlgebra

end LeanCategories.ForMathlib
