/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.QuotientManifold
public import LeanCategories.Lattices.Valued.ComplexStructure
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Complex tori as Lie groups

`LeanCategories.ForMathlib.QuotientManifold` makes `E ⧸ L` a `C^n` manifold for a discrete
subgroup `L` of a normed space `E`, and `LeanCategories.Lattices.Valued.ComplexStructure` supplies
complex structures and Riemann forms. This file joins the two.

## Main results

* `ComplexStructure.IsCircleIsometric`: the norm hypothesis on a complex structure that makes the
  induced `ℂ`-action bounded, and `ComplexStructure.normedSpace`, the resulting `NormedSpace ℂ E`.
* `contMDiff_quotientMk`: the projection `E → E ⧸ L` is `C^n`.
* `instLieAddGroupQuotient`: `E ⧸ L` is an additive Lie group.
* `ComplexTorus`: a bundled complex torus, and `IsAbelianVariety`, the predicate that it carries a
  Riemann form integral on the period lattice.

## The norm hypothesis

`ComplexStructure.module` makes `E` a `ℂ`-module but *not* a `NormedSpace ℂ E`, and requiring `J`
to be a norm isometry does not repair this. Take `E = ℝ²` with the supremum norm and
`J (a, b) = (-b, a)`; then `J` is an isometry, but for `z = 1 + i` and `x = (1, 1)` one has
`z • x = (0, 2)`, of norm `2`, while `‖z‖ * ‖x‖ = √2`. The bound `‖z • x‖ ≤ ‖z‖ * ‖x‖` fails.

The correct hypothesis is that the whole unit circle acts by isometries, which is
`ComplexStructure.IsCircleIsometric` below: `‖a • x + b • J x‖ = ‖x‖` whenever `a² + b² = 1`.
Taking `a = 0`, `b = 1` recovers the isometry of `J`, so the condition is strictly stronger, and
it is exactly what makes `‖z • x‖ = ‖z‖ * ‖x‖`. Every `ℂ`-normed space satisfies it for its own
complex structure (`ComplexStructure.isCircleIsometric_ofComplexModule`), so the hypothesis is not
vacuous.

## Smoothness of the projection

The projection is locally a chart inverse. On the preimage of a chart source, `e ∘ mk` moves every
point by an element of `L`, so it is `C^n` by `contDiffOn_of_sub_mem`, and `mk = e.symm ∘ (e ∘ mk)`
there. The Lie group structure follows: addition and negation on `E ⧸ L` factor through charts,
the corresponding operations on `E`, and the projection.

## Mathlib coverage

Mathlib has no complex torus, no Riemann form and no abelian variety. It supplies the Lie group
class `LieAddGroup`, the `ℤ`-lattice API `IsZLattice`, and the chart smoothness lemmas used here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Lattices.Valued

open LeanCategories.ForMathlib
open scoped ContDiff Manifold

universe u

/-! ## The norm hypothesis on a complex structure -/

namespace ComplexStructure

section CircleIsometric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A complex structure whose induced unit circle acts by isometries: `a • x + b • J x` has the
norm of `x` whenever `a² + b² = 1`. This is what upgrades `ComplexStructure.module` to a
`NormedSpace ℂ E`; isometry of `J` alone does not. -/
structure IsCircleIsometric (Jstr : ComplexStructure E) : Prop where
  /-- Points of the unit circle act by isometries. -/
  norm_circle_smul : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → ∀ x : E, ‖a • x + b • Jstr.J x‖ = ‖x‖

variable {Jstr : ComplexStructure E}

/-- A circle-isometric complex structure has `J` an isometry. -/
theorem IsCircleIsometric.norm_J (h : IsCircleIsometric Jstr) (x : E) : ‖Jstr.J x‖ = ‖x‖ := by
  simpa using h.norm_circle_smul 0 1 (by norm_num) x

/-- Under the circle hypothesis the induced complex action multiplies norms. -/
theorem IsCircleIsometric.norm_smul (h : IsCircleIsometric Jstr) (z : ℂ) (x : E) :
    letI := Jstr.module
    ‖z • x‖ = ‖z‖ * ‖x‖ := by
  letI := Jstr.module
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hr : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : ‖z‖ * (z.re / ‖z‖) = z.re := by field_simp
  have h2 : ‖z‖ * (z.im / ‖z‖) = z.im := by field_simp
  have hsq : (z.re / ‖z‖) ^ 2 + (z.im / ‖z‖) ^ 2 = 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    field_simp
    nlinarith [this]
  have key : z • x = ‖z‖ • ((z.re / ‖z‖) • x + (z.im / ‖z‖) • Jstr.J x) := by
    rw [Jstr.module_smul, smul_add, smul_smul, smul_smul, h1, h2]
  rw [key, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos hr, h.norm_circle_smul _ _ hsq x]

/-- The `NormedSpace ℂ E` supplied by a circle-isometric complex structure. This is the piece
`ComplexStructure.module` alone does not provide. -/
@[reducible]
def normedSpace (h : IsCircleIsometric Jstr) : NormedSpace ℂ E :=
  letI := Jstr.module
  { Jstr.module with
    norm_smul_le := fun z x => le_of_eq (h.norm_smul z x) }

/-- The complex structure of a complex normed space: multiplication by `i`. -/
def ofComplexModule (V : Type u) [AddCommGroup V] [Module ℂ V] : ComplexStructure V where
  J := (LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ
  sq := by
    ext x
    simp [smul_smul, Complex.I_mul_I]

/-- The complex structure of a complex module is multiplication by `i`. -/
@[simp]
theorem ofComplexModule_J (V : Type u) [AddCommGroup V] [Module ℂ V] (x : V) :
    (ofComplexModule V).J x = Complex.I • x := rfl

/-- Multiplication by `i` on a complex normed space is circle isometric, so the hypothesis of
`ComplexStructure.normedSpace` is satisfiable. -/
theorem isCircleIsometric_ofComplexModule (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V] :
    IsCircleIsometric (ofComplexModule V) := by
  refine ⟨fun a b hab x => ?_⟩
  have hsmul : ∀ (r : ℝ) (v : V), r • v = (r : ℂ) • v := fun r v =>
    (algebraMap_smul ℂ r v).symm
  have hz : a • x + b • (ofComplexModule V).J x = ((a : ℂ) + (b : ℂ) * Complex.I) • x := by
    rw [ofComplexModule_J, hsmul a x, hsmul b (Complex.I • x), smul_smul, add_smul]
  have hnorm : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ = 1 := by
    have : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      nlinarith [hab]
    nlinarith [norm_nonneg ((a : ℂ) + (b : ℂ) * Complex.I), this]
  rw [hz, norm_smul, hnorm, one_mul]

end CircleIsometric

end ComplexStructure

/-! ## Smoothness of the projection -/

section Projection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (L : Submodule ℤ E) [DiscreteTopology L]

/-- The projection `E → E ⧸ L` is `C^n` as a map of manifolds, for every smoothness exponent.
On the preimage of a chart source it is that chart's inverse composed with a translation-like
`C^n` self map of `E`. -/
theorem contMDiff_quotientMk (n : ℕ∞ω) :
    ContMDiff (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) n
      (Submodule.Quotient.mk : E → E ⧸ L) := by
  intro u
  set q : E ⧸ L := Submodule.Quotient.mk u with hq
  set e := chartAt E q with he
  set s : Set E := (Submodule.Quotient.mk : E → E ⧸ L) ⁻¹' e.source with hs
  have hcont : Continuous (Submodule.Quotient.mk : E → E ⧸ L) := (isLocalHomeomorph_mk L).continuous
  have hsopen : IsOpen s := e.open_source.preimage hcont
  have hus : u ∈ s := ChartedSpace.mem_chart_source (H := E) q
  have hsub : ∀ x ∈ s, (⇑e ∘ (Submodule.Quotient.mk : E → E ⧸ L)) x - x ∈ L := by
    intro x hx
    exact (Submodule.Quotient.eq L).mp (mk_chart_apply (chart_mem_atlas E q) hx)
  have hg : ContDiffOn 𝕜 n (⇑e ∘ (Submodule.Quotient.mk : E → E ⧸ L)) s :=
    contDiffOn_of_sub_mem (L := L)
      (e.continuousOn.comp hcont.continuousOn (Set.mapsTo_preimage _ _)) hsub
  have hmaps : Set.MapsTo (⇑e ∘ (Submodule.Quotient.mk : E → E ⧸ L)) s e.target :=
    fun x hx => e.mapsTo hx
  have hcomp : ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) n
      (⇑e.symm ∘ ⇑e ∘ (Submodule.Quotient.mk : E → E ⧸ L)) s :=
    (contMDiffOn_chart_symm (I := modelWithCornersSelf 𝕜 E) (n := n) (x := q)).comp
      hg.contMDiffOn hmaps
  have hmk : ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) n
      (Submodule.Quotient.mk : E → E ⧸ L) s :=
    hcomp.congr fun x hx => (e.left_inv hx).symm
  exact hmk.contMDiffAt (hsopen.mem_nhds hus)

/-- Addition on `E ⧸ L` is `C^n`: through charts it is addition on `E` followed by the
projection. -/
instance instContMDiffAddQuotient (n : ℕ∞ω) :
    ContMDiffAdd (modelWithCornersSelf 𝕜 E) n (E ⧸ L) where
  contMDiff_add := by
    intro p
    set e₁ := chartAt E p.1 with he₁
    set e₂ := chartAt E p.2 with he₂
    set s : Set ((E ⧸ L) × (E ⧸ L)) := e₁.source ×ˢ e₂.source with hs
    have hsopen : IsOpen s := e₁.open_source.prod e₂.open_source
    have hps : p ∈ s :=
      ⟨ChartedSpace.mem_chart_source (H := E) p.1, ChartedSpace.mem_chart_source (H := E) p.2⟩
    have hchart : ContMDiffOn
        ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E))
        ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E)) n
        (Prod.map ⇑e₁ ⇑e₂) s :=
      (contMDiffOn_chart (I := modelWithCornersSelf 𝕜 E) (n := n) (x := p.1)).prodMap
        (contMDiffOn_chart (I := modelWithCornersSelf 𝕜 E) (n := n) (x := p.2))
    have hadd := (contMDiff_add (modelWithCornersSelf 𝕜 E) n (G := E)).comp_contMDiffOn hchart
    have hres := (contMDiff_quotientMk L n).comp_contMDiffOn hadd
    have heq : ContMDiffOn
        ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E))
        (modelWithCornersSelf 𝕜 E) n (fun r : (E ⧸ L) × (E ⧸ L) => r.1 + r.2) s := by
      refine hres.congr fun r hr => ?_
      have h₁ : (Submodule.Quotient.mk (e₁ r.1) : E ⧸ L) = r.1 :=
        mk_chart_apply (chart_mem_atlas E p.1) hr.1
      have h₂ : (Submodule.Quotient.mk (e₂ r.2) : E ⧸ L) = r.2 :=
        mk_chart_apply (chart_mem_atlas E p.2) hr.2
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, Submodule.Quotient.mk_add,
        h₁, h₂]
    exact heq.contMDiffAt (hsopen.mem_nhds hps)

/-- `E ⧸ L` is an additive Lie group for every smoothness exponent: it is a manifold, and
addition and negation are `C^n` because they lift through the projection. -/
instance instLieAddGroupQuotient (n : ℕ∞ω) :
    LieAddGroup (modelWithCornersSelf 𝕜 E) n (E ⧸ L) where
  contMDiff_neg := by
    intro q
    set e := chartAt E q with he
    have hsopen : IsOpen e.source := e.open_source
    have hqs : q ∈ e.source := ChartedSpace.mem_chart_source (H := E) q
    have hchart : ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) n
        (⇑e) e.source :=
      contMDiffOn_chart (I := modelWithCornersSelf 𝕜 E) (n := n) (x := q)
    have hneg := (contMDiff_neg (modelWithCornersSelf 𝕜 E) n (G := E)).comp_contMDiffOn hchart
    have hres := (contMDiff_quotientMk L n).comp_contMDiffOn hneg
    have heq : ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E) n
        (fun r : E ⧸ L => -r) e.source := by
      refine hres.congr fun r hr => ?_
      have h₁ : (Submodule.Quotient.mk (e r) : E ⧸ L) = r := mk_chart_apply (chart_mem_atlas E q) hr
      simp only [Function.comp_apply, Submodule.Quotient.mk_neg, h₁]
    exact heq.contMDiffAt (hsopen.mem_nhds hqs)

end Projection

/-! ## The manifold structure from a complex structure -/

section FromComplexStructure

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gap closed: a circle-isometric complex structure on a real normed space makes every quotient
by a discrete subgroup a complex manifold. The `NormedSpace ℂ E` needed by the model
`𝓘(ℂ, E)` is the one built from the complex structure. -/
theorem isManifold_quotient_of_isCircleIsometric {Jstr : ComplexStructure E}
    (h : Jstr.IsCircleIsometric) (L : Submodule ℤ E) [DiscreteTopology L] (n : ℕ∞ω) :
    letI := Jstr.module
    letI := ComplexStructure.normedSpace h
    IsManifold (modelWithCornersSelf ℂ E) n (E ⧸ L) := by
  letI := Jstr.module
  letI := ComplexStructure.normedSpace h
  infer_instance

end FromComplexStructure

/-! ## Complex tori and abelian varieties -/

/-- A complex torus: a finite-dimensional complex normed space modulo a discrete lattice of full
rank. The quotient is a compact complex manifold and an additive Lie group. -/
structure ComplexTorus where
  /-- The ambient complex vector space. -/
  V : Type u
  [normedAddCommGroup : NormedAddCommGroup V]
  [normedSpace : NormedSpace ℂ V]
  [finiteDimensional : FiniteDimensional ℂ V]
  /-- The period lattice. -/
  lattice : Submodule ℤ V
  [discreteTopology : DiscreteTopology lattice]
  [isZLattice : IsZLattice ℝ lattice]

attribute [instance] ComplexTorus.normedAddCommGroup ComplexTorus.normedSpace
  ComplexTorus.finiteDimensional ComplexTorus.discreteTopology ComplexTorus.isZLattice

namespace ComplexTorus

/-- The underlying manifold of a complex torus. -/
abbrev carrier (T : ComplexTorus.{u}) : Type u := T.V ⧸ T.lattice

instance (T : ComplexTorus.{u}) : FiniteDimensional ℝ T.V :=
  Module.Finite.trans ℂ T.V

/-- A complex torus is compact: its lattice has full rank. -/
instance (T : ComplexTorus.{u}) : CompactSpace T.carrier := by
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr T.lattice.mkQ_surjective]
  refine IsZLattice.isCompact_range_of_periodic T.lattice _ (Submodule.continuous_mkQ _) ?_
  intro z w hw
  simpa [Submodule.Quotient.eq] using hw

/-- A complex torus is a complex manifold. -/
theorem isManifold (T : ComplexTorus.{u}) (n : ℕ∞ω) :
    IsManifold (modelWithCornersSelf ℂ T.V) n T.carrier :=
  inferInstance

/-- A complex torus is an additive Lie group. -/
theorem lieAddGroup (T : ComplexTorus.{u}) (n : ℕ∞ω) :
    LieAddGroup (modelWithCornersSelf ℂ T.V) n T.carrier :=
  inferInstance

end ComplexTorus

/-- A complex torus is an abelian variety when it carries a Riemann form that is integral on the
period lattice. These are the Riemann relations; they are equivalent to the torus being a
projective algebraic variety, a theorem not proved here. -/
def IsAbelianVariety (T : ComplexTorus.{u}) : Prop :=
  ∃ b : LinearMap.BilinForm ℝ T.V,
    ComplexStructure.IsRiemannForm b (ComplexStructure.ofComplexModule T.V) ∧
      ∀ x ∈ T.lattice, ∀ y ∈ T.lattice, ∃ m : ℤ, b x y = (m : ℝ)

/-- The Gaussian torus `ℂ / (ℤ + ℤ i)`, the square elliptic curve. -/
abbrev gaussianTorus : ComplexTorus.{0} where
  V := ℂ
  lattice := Submodule.span ℤ (Set.range Complex.basisOneI)

/-- The imaginary part of `conj x * y`, as a real bilinear form on `ℂ`. This is the standard
Riemann form of the square elliptic curve. -/
def gaussianForm : LinearMap.BilinForm ℝ ℂ :=
  LinearMap.mk₂ ℝ (fun x y : ℂ => x.re * y.im - x.im * y.re)
    (fun x₁ x₂ y => by simp only [Complex.add_re, Complex.add_im]; ring)
    (fun r x y => by
      simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul]; ring)
    (fun x y₁ y₂ => by simp only [Complex.add_re, Complex.add_im]; ring)
    (fun r x y => by
      simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul]; ring)

/-- The Gaussian form evaluates to `Im (conj x * y)`. -/
@[simp]
theorem gaussianForm_apply (x y : ℂ) : gaussianForm x y = x.re * y.im - x.im * y.re := rfl

/-- Every element of the Gaussian lattice is `a + b i` with `a b : ℤ`. -/
theorem mem_gaussianLattice {z : ℂ} (hz : z ∈ Submodule.span ℤ (Set.range Complex.basisOneI)) :
    ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * Complex.I := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | smul m x _ hx =>
    obtain ⟨a, b, rfl⟩ := hx
    exact ⟨m * a, m * b, by push_cast [zsmul_eq_mul]; ring⟩

/-- The Gaussian torus is an abelian variety: `Im (conj x * y)` is a Riemann form, integral on
`ℤ + ℤ i`. So `IsAbelianVariety` is not vacuous. -/
theorem isAbelianVariety_gaussianTorus : IsAbelianVariety gaussianTorus := by
  have hJ : ∀ w : ℂ, (ComplexStructure.ofComplexModule ℂ).J w = Complex.I * w := fun _ => rfl
  refine ⟨gaussianForm, ⟨fun x => ?_, fun x y => ?_, fun x hx => ?_⟩, ?_⟩
  · simp only [gaussianForm_apply]; ring
  · simp only [gaussianForm_apply, hJ, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  · simp only [gaussianForm_apply, hJ, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    have hpos : 0 < Complex.normSq x := Complex.normSq_pos.mpr hx
    rw [Complex.normSq_apply] at hpos
    nlinarith [hpos]
  · intro x hx y hy
    obtain ⟨a, b, rfl⟩ := mem_gaussianLattice hx
    obtain ⟨c, d, rfl⟩ := mem_gaussianLattice hy
    refine ⟨a * d - b * c, ?_⟩
    simp only [gaussianForm_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    push_cast
    ring

end LeanCategories.Lattices.Valued
