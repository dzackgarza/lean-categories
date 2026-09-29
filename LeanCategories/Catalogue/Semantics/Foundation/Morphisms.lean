/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.Objects
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Elements and morphisms of named sets

* Element literals: the numeral `k` names `k ∈ ℕ`, `k ∈ ℤ`, `k ∈ Fin n` when `k < n`, and
  `k mod n ∈ ℤ/n`.
* Graph literals of `Sets`: a finite list of pairs `(x, y)` listing each element of `X` exactly
  once is the function `X → Y` with that graph (`{0 ↦ 1, 1 ↦ 0} : Fin 2 → Fin 2`).
* The named morphism family `rev : Fin n → Fin n`, `k ↦ n - 1 - k` (Mathlib `Fin.rev`).
-/

namespace CasCatalogue.Foundation.Morphisms

open CasCatalogue.Foundation.Objects

universe u

/-- `k ∈ ℕ`. -/
def naturalsElement (k : ℕ) : Option naturals := some k

/-- `k ∈ ℤ`. -/
def integersElement (k : ℕ) : Option integers := some (k : ℤ)

/-- `k ∈ Fin n`, when `k < n`. -/
def finElement (n k : ℕ) : Option (fin n) := if h : k < n then some (⟨k, h⟩ : Fin n) else none

/-- `k mod n ∈ ℤ/n`. -/
def integersModElement (n k : ℕ) : Option (integersMod n) := some (k : ZMod n)

/-- The value at `x` of the function whose graph `l` lists `x`. -/
def graphValue {X Y : Type u} [DecidableEq X] :
    (l : List (X × Y)) → (x : X) → x ∈ l.map Prod.fst → Y
  | [], _, h => absurd h List.not_mem_nil
  | (a, b) :: l, x, h =>
      if hx : x = a then b else graphValue l x ((List.mem_cons.mp h).resolve_left hx)

/-- The function `X → Y` with graph `l`, which lists each element of `X` exactly once. -/
def ofGraph {X Y : Type u} [DecidableEq X]
    (l : List (X × Y)) (total : ∀ x, x ∈ l.map Prod.fst) (_nodup : (l.map Prod.fst).Nodup) :
    (X : LeanCategories.Foundation.Mathlib.Sets.{u}) ⟶
      (Y : LeanCategories.Foundation.Mathlib.Sets.{u}) :=
  TypeCat.ofHom fun x => graphValue l x (total x)

/-- `Fin.rev : Fin n → Fin n`. -/
def finRev (n : ℕ) : fin n ⟶ fin n := TypeCat.ofHom Fin.rev

theorem graphValue_mem {X Y : Type u} [DecidableEq X] (l : List (X × Y)) (x : X)
    (h : x ∈ l.map Prod.fst) : (x, graphValue l x h) ∈ l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons p l ih =>
      obtain ⟨a, b⟩ := p
      unfold graphValue
      split_ifs with hx
      · subst hx; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _)

end CasCatalogue.Foundation.Morphisms

namespace CasCatalogue

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.naturals"⟩, object := ⟨"obj.sets.naturals"⟩
    denotation := `CasCatalogue.Foundation.Morphisms.naturalsElement }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.integers"⟩, object := ⟨"obj.sets.integers"⟩
    denotation := `CasCatalogue.Foundation.Morphisms.integersElement }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.fin"⟩, object := ⟨"obj.sets.fin"⟩
    denotation := `CasCatalogue.Foundation.Morphisms.finElement }

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.integers_mod"⟩, object := ⟨"obj.sets.integers_mod"⟩
    denotation := `CasCatalogue.Foundation.Morphisms.integersModElement }

normalized_registry .graphLiteral
  { id := ⟨"graph.sets"⟩, category := CategoryId.sets
    denotation := `CasCatalogue.Foundation.Morphisms.ofGraph }

normalized_registry .morphism
  { id := ⟨"mor.sets.fin_rev"⟩, category := CategoryId.sets, name := "rev"
    declaration := `CasCatalogue.Foundation.Morphisms.finRev }

end CasCatalogue
