import Sharpness.ComplexExtensionColimits
import Sharpness.ExtendCycleClasses
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Actual extension/cokernel comparison formulas, including the
degreewise quotient map on a specified representative. -/
set_option autoImplicit false
noncomputable section
universe u t t'
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')
    {A B : HomologicalComplex (ModuleCat.{u} R) c} (f : A ⟶ B)

def extensionCokernelIso :
    cokernel (HomologicalComplex.extendMap f e) ≅ (cokernel f).extend e :=
  (PreservesCokernel.iso (e.extendFunctor (ModuleCat.{u} R)) f).symm

theorem extensionCokernelIso_projection :
    cokernel.π (HomologicalComplex.extendMap f e) ≫ (extensionCokernelIso e f).hom =
      HomologicalComplex.extendMap (cokernel.π f) e := by
  have h := PreservesCokernel.π_iso_hom (e.extendFunctor (ModuleCat.{u} R)) f
  calc
    _ = (HomologicalComplex.extendMap (cokernel.π f) e ≫
        (PreservesCokernel.iso (e.extendFunctor (ModuleCat.{u} R)) f).hom) ≫
          (PreservesCokernel.iso (e.extendFunctor (ModuleCat.{u} R)) f).inv :=
      congrArg (fun t => t ≫ (PreservesCokernel.iso (e.extendFunctor (ModuleCat.{u} R)) f).inv) h.symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun t => HomologicalComplex.extendMap (cokernel.π f) e ≫ t)
        (PreservesCokernel.iso (e.extendFunctor (ModuleCat.{u} R)) f).hom_inv_id).trans
          (Category.comp_id _))

set_option backward.isDefEq.respectTransparency false in
theorem extensionCokernelIso_projection_component (i : ι) (i' : ι') (hi : e.f i=i') :
    (cokernel.π (HomologicalComplex.extendMap f e)).f i' ≫ (extensionCokernelIso e f).hom.f i' ≫
        ((cokernel f).extendXIso e hi).hom =
      (B.extendXIso e hi).hom ≫ (cokernel.π f).f i := by
  have h := HomologicalComplex.congr_hom (extensionCokernelIso_projection e f) i'
  have he := HomologicalComplex.extendMap_f (cokernel.π f) e hi
  calc
    _ = (HomologicalComplex.extendMap (cokernel.π f) e).f i' ≫
        ((cokernel f).extendXIso e hi).hom := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ ((cokernel f).extendXIso e hi).hom) h)
    _ = _ := by rw [he]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Sharpness
