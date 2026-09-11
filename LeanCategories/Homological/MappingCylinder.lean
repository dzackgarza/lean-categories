/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Mapping cylinders of chain maps

Weibel, *An Introduction to Homological Algebra* (1994), Construction 1.5.5,
FC05-C01-U043.

For a chain map `f : B ⟶ D`, Weibel's mapping cylinder has
`cyl(f)_n = B_n ⊕ B_(n-1) ⊕ D_n` and differential
`(b,b',d) ↦ (db+b', -db', dd-fb')`. It is realized here without a parallel
chain-complex implementation: it is the homotopy cofiber of the canonical map
`(id_B,-f) : B ⟶ B ⊞ D` already supported by Mathlib. The degreewise
biproduct isomorphism and the two differential projection formulas below give
exactly the source coordinates and signs.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {B D : ChainComplex C ℤ}

/-- The map `(id_B, -f) : B → B ⊞ D` whose homotopy cofiber is Weibel's mapping cylinder. -/
noncomputable def mappingCylinderMap (f : B ⟶ D) : B ⟶ B ⊞ D :=
  biprod.lift (𝟙 B) (-f)

/-- Weibel's mapping cylinder of a chain map `f : B ⟶ D`, realized as the homotopy cofiber
of `(id_B, -f) : B → B ⊞ D`. -/
noncomputable def mappingCylinder (f : B ⟶ D) : ChainComplex C ℤ :=
  HomologicalComplex.homotopyCofiber (mappingCylinderMap f)

/-- Weibel's chain mapping cone, with differential `(db, dd - f b)`, is the
Mathlib homotopy cofiber of `-f`. The minus sign is part of the source convention. -/
noncomputable def chainMappingCone (f : B ⟶ D) : ChainComplex C ℤ :=
  HomologicalComplex.homotopyCofiber (-f)

namespace mappingCylinder

@[reassoc (attr := simp)]
theorem map_fst (f : B ⟶ D) : mappingCylinderMap f ≫ biprod.fst = 𝟙 B := by
  simp [mappingCylinderMap]

@[reassoc (attr := simp)]
theorem map_snd (f : B ⟶ D) : mappingCylinderMap f ≫ biprod.snd = -f := by
  simp [mappingCylinderMap]

-- Separating boundary: for a nonidentity endomap this is not the ordinary cylinder map.
example {B : ChainComplex C ℤ} (f : B ⟶ B) (hf : f ≠ 𝟙 B) :
    mappingCylinderMap f ≠ biprod.lift (𝟙 B) (-𝟙 B) := by
  intro h
  have h' := congrArg (fun g => g ≫ (biprod.snd : B ⊞ B ⟶ B)) h
  simp only [map_snd, biprod.lift_snd] at h'
  exact hf (neg_injective h')

/-- The canonical embedded copy of `B` in the mapping cylinder. -/
noncomputable def inB (f : B ⟶ D) : B ⟶ mappingCylinder f :=
  (biprod.inl : B ⟶ B ⊞ D) ≫
    HomologicalComplex.homotopyCofiber.inr (mappingCylinderMap f)

/-- The canonical embedded copy of `D` in the mapping cylinder. -/
noncomputable def inD (f : B ⟶ D) : D ⟶ mappingCylinder f :=
  (biprod.inr : D ⟶ B ⊞ D) ≫
    HomologicalComplex.homotopyCofiber.inr (mappingCylinderMap f)

/-- In degree `n`, the structural homotopy-cofiber presentation is canonically
`B_(n-1) ⊞ (B_n ⊞ D_n)`. -/
noncomputable def xIsoCofiberOrder (f : B ⟶ D) (n : ℤ) :
    (mappingCylinder f).X n ≅ B.X (n - 1) ⊞ (B.X n ⊞ D.X n) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (mappingCylinderMap f) n (n - 1) (by simp) ≪≫
    biprod.mapIso (Iso.refl _) (HomologicalComplex.biprodXIso B D n)

/-- Reordering the biproduct factors gives Weibel's displayed degree
`B_n ⊞ B_(n-1) ⊞ D_n`. -/
noncomputable def xIso (f : B ⟶ D) (n : ℤ) :
    (mappingCylinder f).X n ≅ (B.X n ⊞ B.X (n - 1)) ⊞ D.X n :=
  xIsoCofiberOrder f n ≪≫
    (biprod.associator (B.X (n - 1)) (B.X n) (D.X n)).symm ≪≫
    biprod.mapIso (biprod.braiding (B.X (n - 1)) (B.X n)) (Iso.refl _)

/-- The first cofiber-coordinate differential is `-d_B` on the shifted `B` summand. -/
theorem d_fst (f : B ⟶ D) {i j k : ℤ} (hij : (ComplexShape.down ℤ).Rel i j)
    (hjk : (ComplexShape.down ℤ).Rel j k) :
    (mappingCylinder f).d i j ≫
        HomologicalComplex.homotopyCofiber.fstX (mappingCylinderMap f) j k hjk =
      -HomologicalComplex.homotopyCofiber.fstX (mappingCylinderMap f) i j hij ≫ B.d j k := by
  exact HomologicalComplex.homotopyCofiber.d_fstX (mappingCylinderMap f) i j k hij hjk

/-- The unshifted `B ⊞ D` coordinate receives the source differential plus the
`(id_B,-f)` contribution from the shifted `B` coordinate. This is the structural form of
Weibel's `(db+b', dc-fb')` formula. -/
theorem d_snd (f : B ⟶ D) {i j : ℤ} (hij : (ComplexShape.down ℤ).Rel i j) :
    (mappingCylinder f).d i j ≫
        HomologicalComplex.homotopyCofiber.sndX (mappingCylinderMap f) j =
      HomologicalComplex.homotopyCofiber.fstX (mappingCylinderMap f) i j hij ≫
          (mappingCylinderMap f).f j +
        HomologicalComplex.homotopyCofiber.sndX (mappingCylinderMap f) i ≫ (B ⊞ D).d i j := by
  exact HomologicalComplex.homotopyCofiber.d_sndX (mappingCylinderMap f) i j hij

/-! ## The cylinder/cone comparison row

Weibel, §1.5 after Exercise 1.5.4 (FC05-C01-U046), constructs the upper row
`0 → B → cyl(f) → cone(f) → 0` of the mapping-cylinder diagram and the map
`β : cyl(f) → D`, `(b,b',d) ↦ f(b)+d`. Exactness and the full commutative
diagram are the separate Lemma 1.5.7 theorem obligation.
-/

theorem downInt_has_prev (j : ℤ) : ∃ i, (ComplexShape.down ℤ).Rel i j :=
  ⟨j + 1, by simp⟩

/-- The commutative square `(id_B, snd)` from `(id_B,-f)` to the source cone map `-f`. -/
noncomputable def toConeArrow (f : B ⟶ D) :
    Arrow.mk (mappingCylinderMap f) ⟶ Arrow.mk (-f) :=
  Arrow.homMk (𝟙 B) (biprod.snd : B ⊞ D ⟶ D) (by simp [mappingCylinderMap])

/-- The quotient map `cyl(f) ⟶ cone(f)` induced by the preceding square. -/
noncomputable def toCone (f : B ⟶ D) : mappingCylinder f ⟶ chainMappingCone f :=
  HomologicalComplex.homotopyCofiber.mapArrowHom
    (mappingCylinderMap f) (-f) downInt_has_prev (toConeArrow f)

/-- Weibel's map `β : cyl(f) ⟶ D`, `(b,b',d) ↦ f(b)+d`. -/
noncomputable def beta (f : B ⟶ D) : mappingCylinder f ⟶ D :=
  HomologicalComplex.homotopyCofiber.desc (mappingCylinderMap f)
    (biprod.desc f (𝟙 D))
    (Homotopy.ofEq (by simp [mappingCylinderMap]))

@[reassoc (attr := simp)]
theorem inB_beta (f : B ⟶ D) : inB f ≫ beta f = f := by
  unfold inB beta LeanCategories.Homological.mappingCylinder
  rw [Category.assoc, HomologicalComplex.homotopyCofiber.inr_desc]
  simp

@[reassoc (attr := simp)]
theorem inD_beta (f : B ⟶ D) : inD f ≫ beta f = 𝟙 D := by
  unfold inD beta LeanCategories.Homological.mappingCylinder
  rw [Category.assoc, HomologicalComplex.homotopyCofiber.inr_desc]
  simp

@[reassoc (attr := simp)]
theorem inB_toCone (f : B ⟶ D) : inB f ≫ toCone f = 0 := by
  unfold inB toCone LeanCategories.Homological.mappingCylinder
    LeanCategories.Homological.chainMappingCone
  dsimp [HomologicalComplex.homotopyCofiber.mapArrowHom]
  rw [Category.assoc, HomologicalComplex.homotopyCofiber.inr_desc]
  simp [toConeArrow]

/-- The upper row `B → cyl(f) → cone(f)` of Weibel's cylinder diagram.
Its exactness is asserted and proved separately in Lemma 1.5.7. -/
noncomputable def coneShortComplex (f : B ⟶ D) : ShortComplex (ChainComplex C ℤ) :=
  ShortComplex.mk (inB f) (toCone f) (inB_toCone f)

end mappingCylinder
end LeanCategories.Homological
