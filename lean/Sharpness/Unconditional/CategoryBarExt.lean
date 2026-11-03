import Sharpness.Unconditional.CategoryBarResolution
import Sharpness.Unconditional.CategoryBarComparison
import Sharpness.Unconditional.ProjectiveCoefficients

/-! The project's old module-valued Ext is computed by the explicit bar
complex, using the projective resolution proved in CategoryBarResolution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- Actual old-style module-valued Ext computed from the explicit resolution. -/
def categoryBarExtIso (M : CoefficientCategory R C) (n : ℕ) :
    higherLimit M n ≅ ((categoryBarComplex R C).linearYonedaObj R M).homology n :=
  categoryBarResolution.isoExt n M

/-- The explicit coefficient cohomology agrees with higher limits in all
degrees, without invoking a published bar-calculation input. -/
def categoryBarCohomologyIso (M : CoefficientCategory R C) (n : ℕ) :
    higherLimit M n ≅ (coefficientCochains M).homology n :=
  categoryBarExtIso M n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
      (categoryBarHomComplexIso M)

set_option maxHeartbeats 800000 in
theorem categoryBarExtIso_naturality {M N : CoefficientCategory R C} (a : M ⟶ N) (n : ℕ) :
    (higherLimitFunctor R C n).map a ≫ (categoryBarExtIso N n).hom =
      (categoryBarExtIso M n).hom ≫
        HomologicalComplex.homologyMap (categoryBarHomComplexMap a) n := by
  change ((((linearYoneda R (CoefficientCategory R C)).map a).rightOp.leftDerived n).app
    (constantCoefficient R C)).unop ≫ _ = _
  rw [categoryBarResolution.leftDerived_app_eq
    ((linearYoneda R (CoefficientCategory R C)).map a).rightOp n]
  dsimp [categoryBarExtIso, ProjectiveResolution.isoExt]
  simp only [unop_comp, Category.assoc, ← Iso.unop_hom, ← Iso.unop_inv,
    Iso.hom_inv_id_assoc]
  congr 1
  have h := (HomologicalComplex.homologyOpNatIso (ModuleCat.{u} R)
    (ComplexShape.up ℕ) n).inv.naturality (categoryBarHomComplexMap a).op
  exact (congrArg Quiver.Hom.unop h).symm

end Sharpness.Unconditional
