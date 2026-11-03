import Sharpness.Unconditional.CentralizerDetectionLocal
import Sharpness.Unconditional.FiberDetection

/-! All-degree higher-limit detection on actual centralizer fusion systems.
The proof uses the concrete cover adjunction, cover equivalence, cartesian
lifts, fiber equivalences, and the derived-limit theorem for fibered categories.
It assumes no reference theorem or spectral-sequence package. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {R : Type u} [CommRing R] [Nontrivial S]

/-- Vanishing in all degrees on every fully centralized nontrivial elementary
abelian centralizer implies vanishing in all degrees on the ambient centric
orbit category. All centralizer systems and comparison maps are constructed. -/
theorem centralizer_higherLimits_zero_of_local
    (D : CoefficientCategory R F.CentricOrbit)
    (zero : ∀ E n, IsZero (higherLimit (F.centralizerRestriction p hS sat D E) n))
    (n : ℕ) : IsZero (higherLimit D n) := by
  letI := F.centralizerCoverFibration_isFibered p sat
  apply IsZero.of_iso _ (F.centralizerCoverHigherLimitIso R p hS sat D n)
  exact covariantHigherLimits_zero_of_fibers R (F.centralizerCoverFibration p)
    ((F.centralizedCoverToCentric p).op ⋙ D)
    (F.centralizer_fiber_higherLimits_zero_of_local p hS sat D zero) n

/-- The same detection statement for any centralizer presentation satisfying
the actual defining morphism predicate, convenient for existing subsystem code. -/
theorem centralizer_higherLimits_zero_of_local_systems
    (C : ∀ E : F.ElementaryCategory p, F.AKOCentralizerInput p hS sat E)
    (D : CoefficientCategory R F.CentricOrbit)
    (zero : ∀ E n, IsZero (higherLimit
      ((F.subsystemCentricFunctor (F.centralizerGroup p E) (C E).system (C E).embedding
        (F.yalcinCentralizerCentricInput p hS sat E (C E)).centric).op ⋙ D) n))
    (n : ℕ) : IsZero (higherLimit D n) := by
  letI := F.centralizerCoverFibration_isFibered p sat
  apply IsZero.of_iso _ (F.centralizerCoverHigherLimitIso R p hS sat D n)
  apply covariantHigherLimits_zero_of_fibers R (F.centralizerCoverFibration p)
    ((F.centralizedCoverToCentric p).op ⋙ D) _ n
  intro E m
  exact IsZero.of_iso (zero E m) (F.centralizerFiberHigherLimitIso R p hS sat E (C E) D m)

end Sharpness.FusionSystem
