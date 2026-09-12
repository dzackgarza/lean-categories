/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct

/-!
# Based simplices and Weibel's elementary homotopy relation

Weibel, *An Introduction to Homological Algebra*, §8.3, pp. 263--269
(FC05-C08-U024).

Pinned Mathlib's `SSet.PtSimplex n x` is exactly the set `Z_n` of `n`-simplices whose every face
is the iterated-degeneracy basepoint.  Its `PtSimplex.RelStruct f g (Fin.last n)` is exactly
Weibel's witness `y`: faces below `n` are the basepoint, face `n` is `f`, and face `n+1` is `g`.
Fibrancy is retained as a source hypothesis; the later proof that this relation is an equivalence
belongs to theorem work.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SSet

universe u

variable (X : SSet.{u}) [KanComplex X]

/-- Weibel's `Z_n(X,*)`: based `n`-simplices all of whose faces are the basepoint.

Source: Weibel, §8.3, pp. 263--269 (FC05-C08-U024). -/
abbrev BasedCycles (n : ℕ) (x : X _⦋0⦌) : Type u := SSet.PtSimplex X n x

/-- Weibel's elementary homotopy relation on `Z_n(X,*)`.

A witness is an `(n+1)`-simplex whose faces `0,...,n-1` are constant at the basepoint, whose
`n`th face is `f`, and whose `(n+1)`st face is `g`.

Source: Weibel, §8.3, pp. 263--269 (FC05-C08-U024). -/
def BasedHomotopyRel {n : ℕ} {x : X _⦋0⦌}
    (f g : BasedCycles X n x) : Prop :=
  Nonempty (PtSimplex.RelStruct f g (Fin.last n))

end SSet
