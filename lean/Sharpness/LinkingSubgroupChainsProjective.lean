import Sharpness.LinkingSubgroupChainReplacement
import Sharpness.ChainReplacementProjective
import Sharpness.SingularChainsProjective

/-! The actual subgroup chain bicomplex and its total have projective
modules in every degree, with no hypothesis on coefficient modules. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]

theorem subgroupChainBicomplex_projective (p q : ℕ) :
    Projective (((L.subgroupChainBicomplex R).X p).X q) := by
  letI : ∀ X n, Projective (((L.subgroupChainDiagram R).obj X).X n) :=
    fun X n => SingularCohomology.chainsFunctor_projective R (L.subgroupDiagram.obj X) n
  exact chainReplacementBicomplex_projective (L.subgroupChainDiagram R) p q

theorem subgroupTotalChains_projective (n : ℕ) :
    Projective ((L.subgroupTotalChains R).X n) := by
  letI : ∀ X n, Projective (((L.subgroupChainDiagram R).obj X).X n) :=
    fun X n => SingularCohomology.chainsFunctor_projective R (L.subgroupDiagram.obj X) n
  exact chainReplacementTotal_projective (L.subgroupChainDiagram R) n

end Sharpness.FusionSystem.CentricLinkingSystem
