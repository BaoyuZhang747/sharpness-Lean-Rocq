import Sharpness.NormalizerChainReplacement
import Sharpness.ChainReplacementProjective
import Sharpness.SingularChainsProjective

/-! The actual normalizer chain bicomplex and its total have projective
modules in every degree, with no hypothesis on coefficient modules. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R]

theorem normalizerChainBicomplex_projective (p q : ℕ) :
    Projective (((I.normalizerChainBicomplex R).X p).X q) := by
  letI : ∀ X n, Projective (((I.normalizerChainDiagram R).obj X).X n) :=
    fun X n => SingularCohomology.chainsFunctor_projective R (I.normalizerDiagram.obj X) n
  exact chainReplacementBicomplex_projective (I.normalizerChainDiagram R) p q

theorem normalizerTotalChains_projective (n : ℕ) :
    Projective ((I.normalizerTotalChains R).X n) := by
  letI : ∀ X n, Projective (((I.normalizerChainDiagram R).obj X).X n) :=
    fun X n => SingularCohomology.chainsFunctor_projective R (I.normalizerDiagram.obj X) n
  exact chainReplacementTotal_projective (I.normalizerChainDiagram R) n

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
