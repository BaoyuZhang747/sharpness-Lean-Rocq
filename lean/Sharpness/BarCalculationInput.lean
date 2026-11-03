import Sharpness.ScalarBar
import Sharpness.PrimeLocalRing
import Sharpness.Unconditional.ProjectiveCoefficients

/-! The finite bar interface, separated from fusion reference data so its
construction can be developed and imported independently. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    [ProjectiveCoefficientInput.{u}]

/-- The finite bar calculation and its general scalar compatibility. -/
class BarCalculationInput where
  model : ∀ (R : Type u) [CommRing R] (J : Type u) [Category.{u} J]
    [Finite J] [∀ X Y : J, Finite (X ⟶ Y)], FiniteBarModel R J
  comparison : ∀ (R : Type u) [CommRing R] (J : Type u) [Category.{u} J]
    [Finite J] [∀ X Y : J, Finite (X ⟶ Y)], (model R J).Comparison
  scalar : ∀ (J : Type u) [Category.{u} J] [Finite J] [∀ X Y : J, Finite (X ⟶ Y)],
    ScalarBarComparison (model (PrimeLocalRing.{u} p) J) (model k J)

end Sharpness
