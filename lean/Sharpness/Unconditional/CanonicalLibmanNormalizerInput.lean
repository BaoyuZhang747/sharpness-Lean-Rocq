import Sharpness.Unconditional.QuillenAChains
import Sharpness.Unconditional.CanonicalLibmanNormalizerData
import Sharpness.Unconditional.NormalizerSubdivisionEvaluationFibres

/-! The full canonical Libman normalizer input. Both native chain comparisons
are proved from the linking-system axioms and the actual category constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
  (L : F.CentricLinkingSystem)

theorem normalizerSubdivisionEvaluation_quasiIso (R : Type u) [CommRing R] :
    QuasiIso ((simplicialChainsFunctor R).map (nerveMap L.normalizerSubdivisionEvaluation)) :=
  nerveMap_quasiIso_of_structured_fibres L.normalizerSubdivisionEvaluation R
    (fun P => L.normalizerEvaluationUnderProjection_quasiIso P (ModuleCat.of R R))

/-- The actual first comparison is the composite of the Grothendieck
projection and the actual initial-object evaluation. -/
theorem normalizerSubdivisionGrothendieckEvaluation_quasiIso
    (R : Type u) [CommRing R] :
    QuasiIso ((simplicialChainsFunctor R).map (nerveMap
      (CostructuredArrow.grothendieckProj L.normalizerSubdivisionProjection ⋙
        L.normalizerSubdivisionEvaluation))) := by
  haveI : QuasiIso ((simplicialChainsFunctor R).map
      (nerveMap (CostructuredArrow.grothendieckProj L.normalizerSubdivisionProjection))) :=
    nerveAdjunction_right_quasiIso
      (costructuredGrothendieckAdjunction L.normalizerSubdivisionProjection) (ModuleCat.of R R)
  haveI := L.normalizerSubdivisionEvaluation_quasiIso R
  change QuasiIso ((simplicialChainsFunctor R).map
    (nerveMap (CostructuredArrow.grothendieckProj L.normalizerSubdivisionProjection) ≫
      nerveMap L.normalizerSubdivisionEvaluation))
  rw [(simplicialChainsFunctor R).map_comp]
  infer_instance

/-- Complete native input with no published-comparison premise. -/
def canonicalLibmanNormalizerInput (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) : L.LibmanNormalizerInput p hS sat :=
  L.libmanNormalizerInputOfEvaluationQuasiIso p hS sat
    L.normalizerSubdivisionGrothendieckEvaluation_quasiIso

theorem canonicalLibmanNormalizerInput_toData (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) :
    (L.canonicalLibmanNormalizerInput p hS sat).toLibmanNormalizerData =
      L.canonicalLibmanNormalizerData := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
