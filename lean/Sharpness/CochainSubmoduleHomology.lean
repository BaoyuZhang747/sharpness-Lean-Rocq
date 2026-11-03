import Sharpness.SubmoduleCochainComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! Homology images of actual subcomplex inclusions. Inclusion of
subcomplexes gives inclusion of these images. A whole subcomplex gives
the whole homology, and zero homology gives the zero image. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.CochainSubmodules
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {T : CochainComplex (ModuleCat.{u} R) ℕ}
    (V : Sharpness.CochainSubmodules T)

theorem map_mono {W : Sharpness.CochainSubmodules T} (h : ∀ i, V.term i ≤ W.term i) :
    Mono (map h) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y he
  exact Subtype.ext (congrArg (fun z : W.term n => z.val) he)

def homologyImage (n : ℕ) : Submodule R (T.homology n) :=
  LinearMap.range (HomologicalComplex.homologyMap V.inclusion n).hom

theorem homologyImage_mono {W : Sharpness.CochainSubmodules T}
    (h : ∀ i, V.term i ≤ W.term i) (n : ℕ) : V.homologyImage n ≤ W.homologyImage n := by
  rintro x ⟨y, rfl⟩
  refine ⟨HomologicalComplex.homologyMap (map h) n y, ?_⟩
  have he : HomologicalComplex.homologyMap (map h) n ≫
      HomologicalComplex.homologyMap W.inclusion n =
        HomologicalComplex.homologyMap V.inclusion n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      (congrArg (fun f => HomologicalComplex.homologyMap f n) (map_inclusion h))
  exact congrArg (fun f => f y) he

theorem inclusion_isIso_of_top (h : ∀ i, V.term i = ⊤) : IsIso V.inclusion := by
  letI : ∀ i, IsIso (V.inclusion.f i) := fun i =>
    (ConcreteCategory.isIso_iff_bijective (V.inclusion.f i)).mpr ⟨
      fun x y he => Subtype.ext he,
      fun x => ⟨⟨x, (h i).symm ▸ Submodule.mem_top⟩, rfl⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components V.inclusion

theorem homologyImage_top (h : ∀ i, V.term i = ⊤) (n : ℕ) : V.homologyImage n = ⊤ := by
  letI := V.inclusion_isIso_of_top h
  letI : IsIso (HomologicalComplex.homologyMap V.inclusion n) :=
    inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map V.inclusion))
  apply LinearMap.range_eq_top.mpr
  exact ((ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstance : IsIso (HomologicalComplex.homologyMap V.inclusion n))).2

theorem homologyImage_eq_bot (n : ℕ) (h : IsZero (V.complex.homology n)) :
    V.homologyImage n = ⊥ := by
  have he : HomologicalComplex.homologyMap V.inclusion n = 0 := h.eq_of_src _ _
  exact (congrArg (fun f => LinearMap.range f.hom) he).trans LinearMap.range_zero

end Sharpness.CochainSubmodules
