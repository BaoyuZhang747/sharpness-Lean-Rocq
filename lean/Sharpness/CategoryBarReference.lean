import Sharpness.CoefficientCochainFunctor
import Sharpness.CoefficientBarFormula

/-! Precise concrete form of the already cited general bar calculation.

AKO III.5.3, pp.171--173, computes higher limits using products over
actual category strings and the alternating coface coboundary. Its
displayed statement is for Ab. The R-module form used here is the same
free-R-module projective-resolution construction, together with the
RC-module Ext description in Yalcin Section 3.1, pp.10--11. This is the
general reference calculation, natural in the coefficient diagram,
including degree zero. It contains no double complex, spectral sequence,
fusion system, linking space, vanishing, convergence or edge assertion.

The complex on the left is constructed in this project. Its term,
differential and coefficient action are explicit, rather than chosen
abstract finite-bar data. See sources/ConcreteBarReferences.* for the
source ranges and MAIN_REFERENCE_BOUNDARY.md for the R-module scope. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable (R C : Type u) [CommRing R] [Category.{u} C]
    [EnoughProjectives (CoefficientCategory R C)]

structure CategoryBarCalculationInput where
  AKO_III_5_3 : ∀ n : ℕ,
    coefficientCohomologyFunctor (R := R) (C := C) n ≅ higherLimitFunctor R C n

end Sharpness
