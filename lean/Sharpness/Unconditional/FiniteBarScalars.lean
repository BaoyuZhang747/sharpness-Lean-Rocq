import Sharpness.Unconditional.FiniteBarConstruction
import Sharpness.ScalarBar

/-! Restricting scalars preserves the actual cochain formula: both sides
are the same products of underlying additive groups with the same signed
sum of coefficient maps. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory Opposite Simplicial

variable {R k C : Type u} [CommRing R] [CommRing k] [Algebra R k]
    [Category.{u} C] [Finite C] [∀ X Y : C, Finite (X ⟶ Y)]

/-- Scalar compatibility of the explicit finite bar model. -/
def finiteCategoryBarScalarComparison :
    ScalarBarComparison (finiteCategoryBarModel R C) (finiteCategoryBarModel k C) where
  cochains M n := AddEquiv.refl _
  differential M n x := by
    change ((coefficientCochains (restrictCoefficientScalars (R := R) M)).d n (n + 1)) x =
      ((coefficientCochains M).d n (n + 1)) x
    simp only [coefficientCochains, AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD,
      ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl

end Sharpness.Unconditional
