import Sharpness.CoefficientZeroCocycles
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Canonical maps between the actual zero-cycle object and the native
inverse limit, specified by all actual category-object projections. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (M : Cᵒᵖ ⥤ ModuleCat.{u} R)

def coefficientLimitZeroCochain : limit M ⟶ (coefficientCochains M).X 0 :=
  ModuleCat.ofHom (LinearMap.pi (fun s => (limit.π M (op (chainHead s))).hom))

@[reassoc]
theorem coefficientLimitZeroCochain_projection (P : C) :
    coefficientLimitZeroCochain M ≫ coefficientZeroEvaluation M P = limit.π M (op P) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem coefficientLimitZeroCochain_closed :
    coefficientLimitZeroCochain M ≫ (coefficientCochains M).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (coefficientZero_closed_iff M _).mpr
  intro P Q f
  exact congrArg (fun t => t x) (limit.w M f.op)

def coefficientLimitToZeroCycles : limit M ⟶ (coefficientCochains M).cycles 0 :=
  (coefficientCochains M).liftCycles (coefficientLimitZeroCochain M) 1
    ((ComplexShape.up ℕ).next_eq' rfl) (coefficientLimitZeroCochain_closed M)

@[reassoc]
theorem coefficientLimitToZeroCycles_inclusion :
    coefficientLimitToZeroCycles M ≫ (coefficientCochains M).iCycles 0 = coefficientLimitZeroCochain M :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
def coefficientZeroCyclesCone : Cone M where
  pt := (coefficientCochains M).cycles 0
  π :=
    { app P := (coefficientCochains M).iCycles 0 ≫ coefficientZeroEvaluation M P.unop
      naturality {P Q} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hx : (coefficientCochains M).d 0 1 ((coefficientCochains M).iCycles 0 x)=0 :=
          congrArg (fun t => t x) ((coefficientCochains M).iCycles_d 0 1)
        exact ((coefficientZero_closed_iff M _).mp hx f.unop).symm }

def coefficientZeroCyclesToLimit : (coefficientCochains M).cycles 0 ⟶ limit M :=
  limit.lift M (coefficientZeroCyclesCone M)

@[reassoc]
theorem coefficientZeroCyclesToLimit_projection (P : C) :
    coefficientZeroCyclesToLimit M ≫ limit.π M (op P) =
      (coefficientCochains M).iCycles 0 ≫ coefficientZeroEvaluation M P :=
  limit.lift_π _ _

end Sharpness
