import Sharpness.ExtensionCokernelClasses

/-! The quotient projection on cohomology commutes with the actual
extension/cokernel comparison. -/
set_option autoImplicit false
noncomputable section
universe u t t'
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') {A B : HomologicalComplex (ModuleCat.{u} R) c} (f : A ⟶ B)

set_option backward.isDefEq.respectTransparency false in
theorem extensionCokernelProjection_cohomology (i : ι) (i' : ι') (hi : e.f i=i') :
    HomologicalComplex.homologyMap (cokernel.π (HomologicalComplex.extendMap f e)) i' ≫
      HomologicalComplex.homologyMap (extensionCokernelIso e f).hom i' ≫
        ((cokernel f).extendHomologyIso e hi).hom =
    (B.extendHomologyIso e hi).hom ≫ HomologicalComplex.homologyMap (cokernel.π f) i := by
  have hc : HomologicalComplex.homologyMap (cokernel.π (HomologicalComplex.extendMap f e)) i' ≫
      HomologicalComplex.homologyMap (extensionCokernelIso e f).hom i' =
    HomologicalComplex.homologyMap (HomologicalComplex.extendMap (cokernel.π f) e) i' :=
      (HomologicalComplex.homologyMap_comp _ _ i').symm.trans
        (congrArg (fun t => HomologicalComplex.homologyMap t i') (extensionCokernelIso_projection e f))
  calc
    _ = HomologicalComplex.homologyMap (HomologicalComplex.extendMap (cokernel.π f) e) i' ≫
        ((cokernel f).extendHomologyIso e hi).hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ ((cokernel f).extendHomologyIso e hi).hom) hc)
    _ = _ := HomologicalComplex.extendHomologyIso_hom_naturality (cokernel.π f) e hi

end Sharpness
