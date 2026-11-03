import Sharpness.LibmanNormalizerInput
import Sharpness.Unconditional.NormalizerSubdivisionConjugacy
import Sharpness.Unconditional.NormalizerSubdivisionCommaQuasiIso

/-! Actual categorical Libman normalizer data from the constructed subdivision.
The second comparison is already proved over every commutative ring.
The separately named intermediate input builder still requires the first
evaluation/Grothendieck comparison; it is not an unconditional full input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

/-- The actual categorical diagram, with its specified comparison functors,
natural subchain transformations, and natural conjugacy isomorphisms. -/
def canonicalLibmanNormalizerData : L.LibmanNormalizerData where
  categoryDiagram := CostructuredArrow.functor L.normalizerSubdivisionProjection
  toLinking := CostructuredArrow.grothendieckProj L.normalizerSubdivisionProjection ⋙
    L.normalizerSubdivisionEvaluation
  chainComparison := L.normalizerSubdivisionChainComparison
  comparison_subchain := L.normalizerSubdivisionComparison_subchain
  comparison_factorization σ := by
    have h := congrArg
      (fun T => L.normalizerSubdivisionChainComparison σ ⋙ T ⋙ L.normalizerSubdivisionEvaluation)
      (costructuredGrothendieckFiber_projection L.normalizerSubdivisionProjection (F.normalizerClass σ))
    exact h.trans (L.normalizerSubdivisionComparison_factorization σ)
  comparison_conjugacy := L.normalizerSubdivisionComparison_conjugacy

/-- The actual chain-comparison map of the canonical data is a quasi-isomorphism.
This is supplied by the constructed comma reflection adjunction. -/
theorem canonicalLibmanNormalizerData_chainComparison_quasiIso
    (R : Type u) [CommRing R] (σ : F.CentricChain) :
    QuasiIso ((simplicialChainsFunctor R).map
      (nerveMapSingleObj (L.ChainAut σ) (L.canonicalLibmanNormalizerData.chainComparison σ))) :=
  L.normalizerSubdivisionChainComparison_quasiIso R σ

/-- The canonical subchain transformation retains the actual initial inclusion. -/
theorem canonicalLibmanNormalizerData_subchain_component
    (σ : F.CentricChain) (m : ℕ) (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    L.normalizerSubdivisionEvaluation.map
      ((L.canonicalLibmanNormalizerData.comparison_subchain σ m e).app
        (SingleObj.star (L.ChainAut σ))).left =
      L.chainInclusion σ (Fin.zero_le (e 0)) :=
  L.normalizerSubdivisionComparison_subchain_component σ m e

/-- Intermediate builder isolating the one remaining Libman comparison.
The explicit premise is the actual evaluation/Grothendieck nerve-chain map,
not a cohomology conclusion; the second comparison is provided by its proof. -/
def libmanNormalizerInputOfEvaluationQuasiIso (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (evaluation_quasiIso : ∀ (R : Type u) [CommRing R],
      QuasiIso ((simplicialChainsFunctor R).map (nerveMap
        (CostructuredArrow.grothendieckProj L.normalizerSubdivisionProjection ⋙
          L.normalizerSubdivisionEvaluation)))) : L.LibmanNormalizerInput p hS sat where
  subdivision := Cat.of L.NormalizerSubdivision
  projection := L.normalizerSubdivisionProjection
  evaluation := L.normalizerSubdivisionEvaluation
  chainComparison := L.normalizerSubdivisionChainComparison
  comparison_subchain := L.normalizerSubdivisionComparison_subchain
  comparison_factorization := L.normalizerSubdivisionComparison_factorization
  comparison_conjugacy := L.normalizerSubdivisionComparison_conjugacy
  Libman_5_1_1_Weibel := evaluation_quasiIso
  Libman_5_1_2_Weibel := L.normalizerSubdivisionChainComparison_quasiIso

theorem libmanNormalizerInputOfEvaluationQuasiIso_toData
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (evaluation_quasiIso : ∀ (R : Type u) [CommRing R],
      QuasiIso ((simplicialChainsFunctor R).map (nerveMap
        (CostructuredArrow.grothendieckProj L.normalizerSubdivisionProjection ⋙
          L.normalizerSubdivisionEvaluation)))) :
    (L.libmanNormalizerInputOfEvaluationQuasiIso p hS sat evaluation_quasiIso).toLibmanNormalizerData =
      L.canonicalLibmanNormalizerData := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
