import LeanCategories.Modules.Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe u

variable (R : Type u) [Ring R]

/-- Finite-rank free `R`-modules. -/
def isFiniteFreeModule : ObjectProperty (ModuleCat.{u} R) :=
  fun M => Module.Free R M ∧ Module.Finite R M

/-- The full subcategory of finite-rank free `R`-modules. -/
abbrev FiniteFreeModuleCat := (isFiniteFreeModule R).FullSubcategory

/-- Inclusion of finite-rank free modules into all modules. -/
def finiteFreeModuleInclusion : FiniteFreeModuleCat R ⥤ ModuleCat.{u} R :=
  (isFiniteFreeModule R).ι

instance finiteFreeModuleInclusion_preservesZeroMorphisms :
    (finiteFreeModuleInclusion R).PreservesZeroMorphisms where
  map_zero := fun _ _ => rfl

/-- A finite-free cover of a module. -/
structure FiniteFreeCover (M : ModuleCat.{u} R) where
  source : FiniteFreeModuleCat R
  map : source.obj ⟶ M
  [epi_map : Epi map]

attribute [instance] FiniteFreeCover.epi_map

/-- Every finitely generated module admits an epimorphism from a finite-rank free module. -/
noncomputable def finiteFreeCover (M : ModuleCat.{u} R) [Module.Finite R M] :
    FiniteFreeCover R M := by
  classical
  let h := Module.Finite.exists_fin' R M
  let n := h.choose
  let f := h.choose_spec.choose
  have hf : Function.Surjective f := h.choose_spec.choose_spec
  let P : FiniteFreeModuleCat R :=
    ⟨ModuleCat.of R (Fin n → R), ⟨inferInstance, inferInstance⟩⟩
  exact
    { source := P
      map := ModuleCat.ofHom f
      epi_map := (ModuleCat.epi_iff_surjective _).2 hf }

/-- Over a Noetherian ring, the kernel of a map out of a finite-free module is finite. -/
noncomputable def finiteFreeKernelCover [IsNoetherianRing R]
    {P : FiniteFreeModuleCat R} {M : ModuleCat.{u} R} (f : P.obj ⟶ M) :
    FiniteFreeCover R (ModuleCat.of R (LinearMap.ker f.hom)) := by
  letI : Module.Finite R P.obj := P.property.2
  letI : IsNoetherian R P.obj := inferInstance
  letI : Module.Finite R (LinearMap.ker f.hom) :=
    Module.Finite.of_fg (IsNoetherian.noetherian (LinearMap.ker f.hom))
  exact finiteFreeCover R (ModuleCat.of R (LinearMap.ker f.hom))

/-- The map from a finite-free cover of `ker f` into the source of `f`. -/
noncomputable def finiteFreeKernelMap [IsNoetherianRing R]
    {P : FiniteFreeModuleCat R} {M : ModuleCat.{u} R} (f : P.obj ⟶ M) :
    (finiteFreeKernelCover R f).source.obj ⟶ P.obj :=
  (finiteFreeKernelCover R f).map ≫ ModuleCat.ofHom (LinearMap.ker f.hom).subtype

@[reassoc (attr := simp)]
theorem finiteFreeKernelMap_comp [IsNoetherianRing R]
    {P : FiniteFreeModuleCat R} {M : ModuleCat.{u} R} (f : P.obj ⟶ M) :
    finiteFreeKernelMap R f ≫ f = 0 := by
  ext x
  simp [finiteFreeKernelMap]

/-- Covering the kernel by a finite-free module is exact at the source of `f`. -/
theorem finiteFreeKernelMap_exact [IsNoetherianRing R]
    {P : FiniteFreeModuleCat R} {M : ModuleCat.{u} R} (f : P.obj ⟶ M) :
    (ShortComplex.mk (finiteFreeKernelMap R f) f (finiteFreeKernelMap_comp R f)).Exact := by
  let c := finiteFreeKernelCover R f
  let e := ModuleCat.kernelIsoKer f
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have h : kernel.lift f (finiteFreeKernelMap R f) (finiteFreeKernelMap_comp R f) =
      c.map ≫ e.inv := by
    rw [← cancel_mono (kernel.ι f), kernel.lift_ι]
    simp [finiteFreeKernelMap, c, e]
  rw [h]
  infer_instance

/-- The inductive step for a finite-free resolution: cover the kernel of the current differential
by another finite-rank free module. -/
noncomputable def finiteFreeResolutionSucc [IsNoetherianRing R]
    {P Q : FiniteFreeModuleCat R} (f : P ⟶ Q) :
    Σ' (X : FiniteFreeModuleCat R) (d : X ⟶ P), d ≫ f = 0 := by
  let f' : P.obj ⟶ Q.obj := f.hom
  let c := finiteFreeKernelCover R f'
  let d : c.source ⟶ P := ObjectProperty.homMk (finiteFreeKernelMap R f')
  refine ⟨c.source, d, ?_⟩
  apply ObjectProperty.hom_ext
  change finiteFreeKernelMap R f' ≫ f' = 0
  exact finiteFreeKernelMap_comp R f'

/-- A noncanonical chain complex of finite-rank free modules resolving a finite module over a
Noetherian ring. -/
noncomputable def finiteFreeResolutionComplex [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : ChainComplex (FiniteFreeModuleCat R) ℕ := by
  let c₀ := finiteFreeCover R M
  let c₁ := finiteFreeKernelCover R c₀.map
  let d₁ : c₁.source ⟶ c₀.source := ObjectProperty.homMk (finiteFreeKernelMap R c₀.map)
  exact ChainComplex.mk' c₀.source c₁.source d₁ (fun f => finiteFreeResolutionSucc R f)

/-- The augmentation of the finite-free resolution. -/
noncomputable def finiteFreeResolutionAugmentation [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (finiteFreeModuleInclusion R).obj ((finiteFreeResolutionComplex R M).X 0) ⟶ M :=
  (finiteFreeCover R M).map

instance finiteFreeResolutionAugmentation_epi [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    Epi (finiteFreeResolutionAugmentation R M) := by
  change Epi (finiteFreeCover R M).map
  exact (finiteFreeCover R M).epi_map

@[reassoc (attr := simp)]
theorem finiteFreeResolution_d_comp_augmentation [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (finiteFreeModuleInclusion R).map ((finiteFreeResolutionComplex R M).d 1 0) ≫
      finiteFreeResolutionAugmentation R M = 0 := by
  change finiteFreeKernelMap R (finiteFreeCover R M).map ≫ (finiteFreeCover R M).map = 0
  exact finiteFreeKernelMap_comp R (finiteFreeCover R M).map

/-- Exactness of the augmented resolution at degree zero. -/
theorem finiteFreeResolution_exact_zero [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (ShortComplex.mk
      ((finiteFreeModuleInclusion R).map ((finiteFreeResolutionComplex R M).d 1 0))
      (finiteFreeResolutionAugmentation R M)
      (finiteFreeResolution_d_comp_augmentation R M)).Exact := by
  change (ShortComplex.mk
    (finiteFreeKernelMap R (finiteFreeCover R M).map)
    (finiteFreeCover R M).map _).Exact
  exact finiteFreeKernelMap_exact R (finiteFreeCover R M).map

end LeanCategories.Homological
