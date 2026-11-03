import Sharpness.Unconditional.InducedCategoryBarNaturality
import Sharpness.Unconditional.InducedCategoryBarComma

/-! Homological cofinality for actual native higher inverse limits, proved
from the actual comma nerves by the induced projective bar resolution. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory
variable (R : Type u) [CommRing R] {C D : Type u}
  [Category.{u} C] [Category.{u} D] (q : C ⥤ D)

/-- The complete comparison is natural in arbitrary coefficient diagrams.
The only geometric hypothesis is acyclicity of the specified comma nerves. -/
def higherLimitNatIsoOfCommaAcyclicity
    (h : ∀ X : D, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (StructuredArrow X q))) (ModuleCat.of R R)))
    (n : ℕ) : higherLimitFunctor R D n ≅
      restrictionCoefficientFunctor R q ⋙ higherLimitFunctor R C n := by
  letI := inducedCategoryBarAugmentationChain_quasiIso_of_comma R q h
  exact higherLimitNatIsoOfInducedBarAugmentation q n

def higherLimitIsoOfCommaAcyclicity
    (h : ∀ X : D, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (StructuredArrow X q))) (ModuleCat.of R R)))
    (M : CoefficientCategory R D) (n : ℕ) :
    higherLimit M n ≅ higherLimit (q.op ⋙ M) n :=
  (higherLimitNatIsoOfCommaAcyclicity R q h n).app M

end Sharpness.Unconditional
