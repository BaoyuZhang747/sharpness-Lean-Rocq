import Sharpness.Unconditional.CentralizerCoverFibration
import Sharpness.Unconditional.FiberKan

/-! Comma categories and strict fibers of the centralizer-cover projection.

The projection is the actual opposite centralizer-cover projection. Its strict
fiber includes in the actual structured-arrow category, with right adjoint
given by cartesian pullback. The generic constructions used below prove the
universal properties; neither an adjunction nor a coherent cleavage is assumed.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V28
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (p : ℕ)

/-- The strict fiber of the centralizer-cover projection. -/
abbrev CentralizerFiber (E : F.ElementaryCategory p) :=
  Fiber (F.centralizerCoverFibration p) E

/-- The actual comma category `E ↓ τ`. -/
abbrev CentralizerComma (E : F.ElementaryCategory p) :=
  StructuredArrow E (F.centralizerCoverFibration p)

/-- The inclusion of the strict fiber into the structured-arrow category. -/
def centralizerKappa (E : F.ElementaryCategory p) :
    CentralizerFiber F p E ⥤ CentralizerComma F p E :=
  fiberToComma (F.centralizerCoverFibration p) E

omit [Finite S] in
/-- Forgetting the comma arrow after the inclusion is the fiber inclusion. -/
theorem centralizerKappa_projection (E : F.ElementaryCategory p) :
    centralizerKappa F p E ⋙ StructuredArrow.proj E (F.centralizerCoverFibration p) =
      Fiber.fiberInclusion (p := F.centralizerCoverFibration p) (S := E) := rfl

/-- The right adjoint formed from the cartesian lifts of the projection. -/
def centralizerNu (sat : F.Saturated p) (E : F.ElementaryCategory p) :
    CentralizerComma F p E ⥤ CentralizerFiber F p E := by
  letI := F.centralizerCoverFibration_isFibered p sat
  exact commaPullback (F.centralizerCoverFibration p) E

/-- The actual adjunction `κ_E ⊣ ν_E`, proved by cartesian factorization. -/
def centralizerKappaAdjunction (sat : F.Saturated p) (E : F.ElementaryCategory p) :
    centralizerKappa F p E ⊣ centralizerNu F p sat E := by
  letI := F.centralizerCoverFibration_isFibered p sat
  exact fiberCommaAdjunction (F.centralizerCoverFibration p) E

/-- Initiality follows from the displayed right adjoint, with its triangle laws. -/
theorem centralizerKappa_initial (sat : F.Saturated p) (E : F.ElementaryCategory p) :
    (centralizerKappa F p E).Initial :=
  Functor.initial_of_adjunction (centralizerKappaAdjunction F p sat E)

variable (R : Type u) [CommRing R]

/-- The actual comma-limit/fiber-limit comparison for any module coefficient. -/
def centralizerCommaLimitIso (sat : F.Saturated p) (E : F.ElementaryCategory p)
    (D : (F.CentralizedCentralizerCover p)ᵒᵖ ⥤ ModuleCat.{u} R) :
    limit (Fiber.fiberInclusion (p := F.centralizerCoverFibration p) (S := E) ⋙ D) ≅
      limit (StructuredArrow.proj E (F.centralizerCoverFibration p) ⋙ D) := by
  letI := F.centralizerCoverFibration_isFibered p sat
  exact fiberCommaLimitIso (F.centralizerCoverFibration p) E D

/-- The right-Kan/fiber computation is natural in the whole coefficient
diagram, so it also compares the differentials of an injective resolution. -/
def centralizerRanEvaluationFiberLimitIso (sat : F.Saturated p)
    (E : F.ElementaryCategory p) :
    (F.centralizerCoverFibration p).ran ⋙
        (evaluation (F.ElementaryCategory p) (ModuleCat.{u} R)).obj E ≅
      (whiskeringLeft (CentralizerFiber F p E)
        (F.CentralizedCentralizerCover p)ᵒᵖ (ModuleCat.{u} R)).obj
          Fiber.fiberInclusion ⋙ lim := by
  letI := F.centralizerCoverFibration_isFibered p sat
  exact ranEvaluationFiberLimitIso R (F.centralizerCoverFibration p) E

end Sharpness.FusionSystem.V28
