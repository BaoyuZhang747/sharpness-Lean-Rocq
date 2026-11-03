import Sharpness.FirstPageRowHomology
import Sharpness.CategoryBarReference

/-! The actual E2 page of the actual replacement spectral sequence is
the native higher limit of the actual vertical cohomology diagram.
Only the general category-bar calculation is a reference parameter. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R C : Type u} [CommRing R] [Category.{u} C]
    [EnoughProjectives (CoefficientCategory R C)]
    (bar : CategoryBarCalculationInput R C)
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

def cochainReplacementSecondPageHigherLimitIso (p q : ℕ) :
    ((totalColumnE₂SpectralSequence (cochainReplacementBicomplex D)).page 2).X (p,q) ≅
      higherLimit (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q) p :=
  cochainReplacementSecondPageIso D p q ≪≫
    (bar.AKO_III_5_3 p).app (D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q)

end Sharpness
