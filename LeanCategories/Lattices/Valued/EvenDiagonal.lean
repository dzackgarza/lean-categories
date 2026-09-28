/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ScaleAndEvenness
public import LeanCategories.Modules.Quadratic.Valued.IsometryClasses
public import LeanCategories.Lattices.Valued.BilRefinements

@[expose] public section

/-!
# Evenness is integrality of the diagonal quadratic form

The diagonal `Δ : Bil_{R,W} ⥤ Quad_{R,W}`, `(M, b) ↦ (M, v ↦ b(v, v))`, carries a formed module to
a quadratic module, and an isometry to an isometry. For a quadratic module with values in `R`,
*`I`-integrality* is value containment: the form lifts through `I ↪ R`. Evenness of an integral
lattice `(L, b)` is the `I = 2R` integrality of `Δ(L, b)` (`isEven_iff_diagonal`), with no
hypothesis on `2`; over `ℤ` it says `2 ∣ b(v, v)` for every `v`.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

section Diagonal

variable (R) (W : Type u) [AddCommGroup W] [Module R W]

/-- The diagonal quadratic module `(M, v ↦ b(v, v))` of a formed module. -/
noncomputable def diagonalObj (L : BilinModuleCat R W) : QuadModuleCat R W :=
  QuadModuleCat.ofQuadraticMap (LinearMap.BilinMap.toQuadraticMap L.bilinMap)

/-- An isometry of formed modules is an isometry of their diagonal quadratic modules. -/
noncomputable def diagonalMap {L M : BilinModuleCat R W} (f : L ⟶ M) :
    diagonalObj R W L ⟶ diagonalObj R W M := by
  refine QuadModuleCat.homMk (Q := diagonalObj R W L) (P := diagonalObj R W M)
    (BilinModuleCat.underlyingMap (L := L) (M := M) f) fun x => ?_
  change LinearMap.BilinMap.toQuadraticMap M.bilinMap (BilinModuleCat.underlyingMap f x) =
    LinearMap.BilinMap.toQuadraticMap L.bilinMap x
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, BilinModuleCat.bilinMap_apply]
  exact BilinModuleCat.map_pairing f x x

theorem underlyingMap_diagonalMap {L M : BilinModuleCat R W} (f : L ⟶ M) :
    QuadModuleCat.underlyingMap (diagonalMap R W f) = BilinModuleCat.underlyingMap f :=
  QuadModuleCat.underlyingMap_homMk (Q := diagonalObj R W L) (P := diagonalObj R W M) _ _

/-- The diagonal `Δ : Bil_{R,W} ⥤ Quad_{R,W}`, `(M, b) ↦ (M, v ↦ b(v, v))`. -/
noncomputable def diagonal : BilinModuleCat R W ⥤ QuadModuleCat R W where
  obj := diagonalObj R W
  map := diagonalMap R W
  map_id L := QuadModuleCat.hom_ext (by
    rw [underlyingMap_diagonalMap, QuadModuleCat.underlyingMap_id]
    rfl)
  map_comp f g := QuadModuleCat.hom_ext (by
    rw [QuadModuleCat.underlyingMap_comp, underlyingMap_diagonalMap, underlyingMap_diagonalMap,
      underlyingMap_diagonalMap]
    rfl)

end Diagonal

/-- `I`-integrality of an `R`-valued quadratic module: its form lifts through `I ↪ R`. -/
def QuadIIntegral (Q : QuadModuleCat R R) (I : Ideal R) : Prop :=
  ∃ qI : QuadraticMap R Q.carrier I, I.subtype.compQuadraticMap qI = Q.form

/-- Evenness of an integral lattice is the `2R`-integrality of its diagonal quadratic form. -/
theorem isEven_iff_diagonal (L : IntegralLatticeCat R) :
    IsEven L ↔ QuadIIntegral ((diagonal R R).obj L.obj) (Ideal.span {(2 : R)}) := by
  unfold IsEven IsIEven QuadIIntegral
  rfl

/-- Evenness of an integral lattice is the evenness classifier of `Bil` at `W = R`:
`b(v, v) ∈ 2R` for every `v` (`bilIsEven`). -/
theorem isEven_iff_exists_two_smul (L : IntegralLatticeCat R) :
    IsEven L ↔ ∀ v, ∃ w : R, quadraticMap L v = (2 : R) • w := by
  rw [IsEven, isIEven_iff_value_mem]
  exact forall_congr' fun v => (exists_two_smul_iff_mem_span _).symm

/-- Over `ℤ`: `L` is even exactly when every `b(v, v)` is divisible by `2`. -/
theorem isEven_iff_two_dvd (L : IntegralLatticeCat ℤ) :
    IsEven L ↔ ∀ v, (2 : ℤ) ∣ quadraticMap L v := by
  rw [IsEven, isIEven_iff_value_mem]
  simp only [Ideal.mem_span_singleton]

end LeanCategories.Lattices.Valued
