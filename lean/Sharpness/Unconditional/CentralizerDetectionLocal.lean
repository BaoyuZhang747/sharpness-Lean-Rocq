import Sharpness.Unconditional.CentralizerDetectionComparison
import Sharpness.Unconditional.CentralizerSaturation

/-! Local coefficients in the actual centralizer fusion system and their
identification with the concrete cover-fibration coefficient fibers. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

/-- The actual centralizer centric orbit inclusion, with centricity proved
from ambient saturation. -/
def centralizerCentricInclusion (E : F.ElementaryCategory p) :
    (F.centralizerSystem p E).CentricOrbit ⥤ F.CentricOrbit :=
  F.subsystemCentricFunctor (F.centralizerGroup p E) (F.centralizerSystem p E)
    (F.akoCentralizerInput p hS sat E).embedding
    (F.yalcinCentralizerCentricInput p hS sat E (F.akoCentralizerInput p hS sat E)).centric

variable {R : Type u} [CommRing R]

/-- Restriction of a coefficient diagram to the actual centralizer orbit category. -/
def centralizerRestriction (D : CoefficientCategory R F.CentricOrbit)
    (E : F.ElementaryCategory p) :
    CoefficientCategory R (F.centralizerSystem p E).CentricOrbit :=
  (F.centralizerCentricInclusion p hS sat E).op ⋙ D

theorem centralizer_fiber_higherLimits_zero_of_local
    (D : CoefficientCategory R F.CentricOrbit)
    (zero : ∀ E n, IsZero (higherLimit (F.centralizerRestriction p hS sat D E) n))
    (E : F.ElementaryCategory p) (n : ℕ) :
    IsZero (covariantHigherLimit R
      (Functor.Fiber.fiberInclusion (p := F.centralizerCoverFibration p) (S := E) ⋙
        ((F.centralizedCoverToCentric p).op ⋙ D)) n) :=
  IsZero.of_iso (zero E n)
    (F.centralizerFiberHigherLimitIso R p hS sat E (F.akoCentralizerInput p hS sat E) D n)

end Sharpness.FusionSystem
