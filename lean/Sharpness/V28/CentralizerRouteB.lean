import Sharpness.V28.CentralizerComma
import Sharpness.Unconditional.CentralizerDetectionLocal
import Sharpness.Unconditional.FiberDetection

/-! All-degree centralizer detection by an injective-resolution argument.

The construction uses the centralizer cover, its fibration and fiber
comparison. The generic fiber theorem uses the following argument:
exact fibre left Kan extension makes restriction preserve injectives; the
coefficient-natural right-Kan comparison makes the right Kan image of an
injective resolution an exact complex of injectives; applying limit gives
vanishing. Lean presents the last step as Hom from the rank-one constant
diagram, identified with limit, and its Ext groups.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V28
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {R : Type u} [CommRing R] [Nontrivial S]

/-- All-degree centralizer detection for arbitrary commutative rings (including the zero
ring), arbitrary coefficient modules, and every degree including zero. -/
theorem centralizer_higherLimits_zero_routeB
    (D : CoefficientCategory R F.CentricOrbit)
    (zero : ∀ E n, IsZero (higherLimit (F.centralizerRestriction p hS sat D E) n))
    (n : ℕ) : IsZero (higherLimit D n) := by
  letI := F.centralizerCoverFibration_isFibered p sat
  apply IsZero.of_iso _ (F.centralizerCoverHigherLimitIso R p hS sat D n)
  exact covariantHigherLimits_zero_of_fibers R (F.centralizerCoverFibration p)
    ((F.centralizedCoverToCentric p).op ⋙ D)
    (F.centralizer_fiber_higherLimits_zero_of_local p hS sat D zero) n

end Sharpness.FusionSystem.V28
