import Sharpness.LinearImageQuotient
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! A cokernel of (u,d) with im(d)=ker(v) is canonically isomorphic
to im(v)/im(vu). This is the linear-algebra step in the stable-page
filtration comparison; no spectral sequence is assumed in this lemma. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {A B D E H : ModuleCat.{u} R}
    (u : B ⟶ A) (d : D ⟶ A) (g : A ⟶ E) (v : A ⟶ H)
    (zero : biprod.desc u d ≫ g = 0)
    (ex : (ShortComplex.mk (biprod.desc u d) g zero).Exact) [Epi g]
    (ker : LinearMap.range d.hom = LinearMap.ker v.hom)

omit [Epi g] in
include zero in
theorem biprodCokernel_u_zero : u ≫ g = 0 := by
  simpa only [← Category.assoc, biprod.inl_desc, comp_zero] using
    congrArg (fun f => biprod.inl ≫ f) zero

omit [Epi g] in
include zero in
theorem biprodCokernel_d_zero : d ≫ g = 0 := by
  simpa only [← Category.assoc, biprod.inr_desc, comp_zero] using
    congrArg (fun f => biprod.inr ≫ f) zero

def imageQuotientProjectionHom : A ⟶ ModuleCat.of R (ImageQuotient u.hom v.hom) :=
  ModuleCat.ofHom (imageQuotientProjection u.hom v.hom)

include ker in
theorem biprodCokernel_projection_zero : biprod.desc u d ≫ imageQuotientProjectionHom u v = 0 := by
  apply biprod.hom_ext'
  · simp only [← Category.assoc, biprod.inl_desc, comp_zero]
    apply ModuleCat.hom_ext
    exact imageQuotientProjection_comp u.hom v.hom
  · simp only [← Category.assoc, biprod.inr_desc, comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact imageQuotientProjection_of_mem_ker u.hom v.hom
      (show d x ∈ v.hom.ker from ker ▸ (show d x ∈ d.hom.range from ⟨x, rfl⟩))

def biprodCokernelImageQuotientMap : E ⟶ ModuleCat.of R (ImageQuotient u.hom v.hom) :=
  ex.desc (imageQuotientProjectionHom u v) (biprodCokernel_projection_zero u d v ker)

theorem biprodCokernelImageQuotientMap_fac :
    g ≫ biprodCokernelImageQuotientMap u d g v zero ex ker = imageQuotientProjectionHom u v :=
  ex.g_desc _ _

def biprodCokernelImageQuotientIso : E ≅ ModuleCat.of R (ImageQuotient u.hom v.hom) := by
  let φ := biprodCokernelImageQuotientMap u d g v zero ex ker
  have fac : φ.hom.comp g.hom = imageQuotientProjection u.hom v.hom :=
    congrArg (fun f => f.hom) (biprodCokernelImageQuotientMap_fac u d g v zero ex ker)
  have hker := imageQuotientProjection_ker_le u.hom v.hom d.hom g.hom
    (congrArg (fun f => f.hom) (biprodCokernel_u_zero u d g zero))
    (congrArg (fun f => f.hom) (biprodCokernel_d_zero u d g zero)) ker
  have bij : Function.Bijective φ := surjective_linear_descent_bijective g.hom
    (imageQuotientProjection u.hom v.hom) φ.hom ((ModuleCat.epi_iff_surjective g).mp inferInstance)
      (imageQuotientProjection_surjective u.hom v.hom) fac hker
  letI : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr bij
  exact asIso φ

end Sharpness
