import Sharpness.FiniteBar

/-! Objectwise-zero coefficients have zero positive actual derived limits,
using the general bar computation already accepted from AKO III.5.3. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FiniteBarModel
open CategoryTheory
variable {R C : Type u} [CommRing R] [Category.{u} C] (B : FiniteBarModel R C)
    (D : CoefficientCategory R C)

theorem exactPositive_of_values_zero (zero : ∀ P, ∀ x : D.obj P, x = 0) : B.ExactPositive D := by
  intro n z _
  refine ⟨0, ?_⟩
  rw [map_zero]
  funext i
  exact (zero _ (z i)).symm

theorem acyclic_of_values_zero [EnoughProjectives (CoefficientCategory R C)]
    (cmp : B.Comparison) (zero : ∀ P, ∀ x : D.obj P, x = 0) : Acyclic D :=
  (B.acyclic_iff cmp D).mpr (B.exactPositive_of_values_zero D zero)

end Sharpness.FiniteBarModel
