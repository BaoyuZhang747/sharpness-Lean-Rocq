import Sharpness.Unconditional.CategoryBarExt
import Sharpness.CategoryBarReference

/-! The natural category bar calculation, discharged by the explicit
projective resolution and cochain identification. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory
variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- Higher limits naturally agree with cohomology of Hom from the proved
projective bar resolution. -/
def categoryBarExtNatIso (n : ℕ) :
    higherLimitFunctor R C n ≅
      categoryBarHomComplexFunctor (R := R) (C := C) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n :=
  NatIso.ofComponents (fun M => categoryBarExtIso M n) (by
    intro M N a
    exact categoryBarExtIso_naturality a n)

/-- The existing explicit coefficient cohomology computes higher limits,
naturally in all coefficient maps and in every degree. -/
def categoryBarCohomologyNatIso (n : ℕ) :
    higherLimitFunctor R C n ≅ coefficientCohomologyFunctor (R := R) (C := C) n :=
  categoryBarExtNatIso n ≪≫ CategoryTheory.Functor.isoWhiskerRight categoryBarHomComplexNatIso
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n)

/-- The formerly published category bar input is now a proved construction. -/
def categoryBarCalculationInput : CategoryBarCalculationInput R C where
  AKO_III_5_3 n := (categoryBarCohomologyNatIso n).symm

end Sharpness.Unconditional
