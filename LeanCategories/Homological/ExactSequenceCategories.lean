/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Categories of short and long exact sequences

Weibel, *An Introduction to Homological Algebra* (1994), Definition preceding
Proposition 1.3.4, pp. 10--14, FC05-C01-U027.

The category `S` of the source is the full subcategory of short complexes of
chain complexes whose objects are short exact. Its morphisms are therefore the
usual commutative diagrams of short exact sequences.

The category `L` is the full subcategory of bi-infinite chain complexes which
are exact at every degree. Its morphisms are chain maps, hence precisely the
commutative ladder diagrams between long exact sequences.

Mathlib already owns all ambient categories, morphisms, and exactness notions;
this file only names the two source categories as their canonical full
subcategories.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe v u

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- Weibel's category `S` of short exact sequences of chain complexes. -/
abbrev ShortExactSequenceCat : Type (max u v) :=
  ObjectProperty.FullSubcategory
    (fun S : ShortComplex (ChainComplex C ℤ) => S.ShortExact)

/-- Weibel's category `L` of long exact sequences. A bi-infinite long exact
sequence is exactly an acyclic `ℤ`-indexed chain complex. -/
abbrev LongExactSequenceCat : Type (max u v) :=
  ObjectProperty.FullSubcategory
    (fun K : ChainComplex C ℤ => K.Acyclic)

-- Intended case: an actual short exact sequence is an object of `S`.
example (S : ShortComplex (ChainComplex C ℤ)) (hS : S.ShortExact) :
    ShortExactSequenceCat C :=
  ⟨S, hS⟩

-- Separating case: a non-short-exact short complex cannot be an object of `S`.
example (S : ShortComplex (ChainComplex C ℤ)) (hS : ¬S.ShortExact) :
    ¬∃ X : ShortExactSequenceCat C, X.obj = S := by
  rintro ⟨X, hX⟩
  apply hS
  rw [← hX]
  exact X.property

-- Intended case: an exact chain complex is an object of `L`.
example (K : ChainComplex C ℤ) (hK : K.Acyclic) :
    LongExactSequenceCat C :=
  ⟨K, hK⟩

-- Separating case: failure of exactness at any degree excludes the sequence from `L`.
example (K : ChainComplex C ℤ) (hK : ¬K.Acyclic) :
    ¬∃ X : LongExactSequenceCat C, X.obj = K := by
  rintro ⟨X, hX⟩
  apply hK
  rw [← hX]
  exact X.property

end LeanCategories.Homological
