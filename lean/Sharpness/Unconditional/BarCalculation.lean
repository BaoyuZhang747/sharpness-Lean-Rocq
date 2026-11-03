import Sharpness.BarCalculationInput
import Sharpness.Unconditional.CategoryBarExt
import Sharpness.Unconditional.FiniteBarScalars

/-! The original finite bar calculation interface is supplied by the explicit
projective bar resolution, its coefficient cochains, and scalar compatibility.
No published-result hypothesis is used in this construction. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory

/-- The finite coefficient bar complex computes the original module-valued
derived inverse limits, with their concrete quotient cohomology. -/
def finiteCategoryBarComparison (R C : Type u) [CommRing R] [Category.{u} C]
    [Finite C] [∀ X Y : C, Finite (X ⟶ Y)] :
    (finiteCategoryBarModel R C).Comparison where
  AKO_III_5_3 M n := categoryBarCohomologyIso M (n + 1) ≪≫
    finiteCategoryBarCohomologyIso M n

/-- Unconditional construction of the manuscript's finite bar input. -/
instance barCalculationInput (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] : BarCalculationInput p k where
  model R _ C _ _ _ := finiteCategoryBarModel R C
  comparison R _ C _ _ _ := finiteCategoryBarComparison R C
  scalar C _ _ _ := finiteCategoryBarScalarComparison

end Sharpness.Unconditional
