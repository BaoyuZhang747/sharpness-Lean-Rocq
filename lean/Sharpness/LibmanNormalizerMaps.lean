import Sharpness.LibmanNormalizerData
import Sharpness.Unconditional.HeterogeneousNerve
import Sharpness.Unconditional.RealizationNerveHomotopy

/-! Actual realized comparison maps for the fixed Libman data. Their
subchain square is an actual homotopy using the deletion homomorphism, and the chain
map to the linking space retains the specified first coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerData
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} (D : L.LibmanNormalizerData)

def chainComparisonMap_subchain (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    TopCat.Homotopy
      (D.chainComparisonMap σ ≫ D.diagram.map (F.normalizerSubchainArrow σ m e))
      (L.chainRestrictionClassifyingMap σ m e ≫ D.chainComparisonMap (σ.subchain m e)) := by
  have h := realizationHomotopy (heterogeneousNerveHomotopy (D.comparison_subchain σ m e))
  have hl : heterogeneousNerveMap
      (D.chainComparison σ ⋙ (D.categoryDiagram.map (F.normalizerSubchainArrow σ m e)).toFunctor) =
      nerveMapSingleObj (L.ChainAut σ) (D.chainComparison σ) ≫
        CategoryTheory.nerveMap (D.categoryDiagram.map (F.normalizerSubchainArrow σ m e)).toFunctor := by
    rw [heterogeneousNerveMap_eq_singleObj, nerveMapSingleObj_comp]
  have hp : heterogeneousNerveMap
      ((L.chainAutRestriction σ m e).toFunctor ⋙ D.chainComparison (σ.subchain m e)) =
      CategoryTheory.nerveMap (L.chainAutRestriction σ m e).toFunctor ≫
        nerveMapSingleObj (L.ChainAut (σ.subchain m e)) (D.chainComparison (σ.subchain m e)) := by
    apply NatTrans.ext
    funext n
    rfl
  rw [hl, hp, SSet.toTop.map_comp, SSet.toTop.map_comp] at h
  exact h

theorem chainComparisonMap_factorization (σ : F.CentricChain) :
    D.chainComparisonMap σ ≫ D.fiberMap (F.normalizerClass σ) ≫ D.grothendieckMap =
      L.chainClassifyingMap σ := by
  have h := congrArg (fun T => nerveMapSingleObj (L.ChainAut σ) T)
    (D.comparison_factorization σ)
  have hn : CategoryTheory.nerveMap
      (Grothendieck.ι D.categoryDiagram (F.normalizerClass σ) ⋙ D.toLinking) =
      CategoryTheory.nerveMap (Grothendieck.ι D.categoryDiagram (F.normalizerClass σ)) ≫
        CategoryTheory.nerveMap D.toLinking := rfl
  rw [nerveMapSingleObj_comp, hn] at h
  change SSet.toTop.map _ ≫ SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp]
  exact congrArg (fun f => SSet.toTop.map f) h

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerData
