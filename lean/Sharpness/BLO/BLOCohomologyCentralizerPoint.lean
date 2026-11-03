import Sharpness.BLO.BLOCohomologyFiber
import Sharpness.BLO.BLODiagramCentralizerBase

/-! The centralizer linking inclusion uses precisely the enlarged objects
whose native restrictions occur in the actual E3 fiber calculation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)

theorem BLOCohomologyCentralizerPair_eq_coverPoint (E : F.ElementaryCategory p)
    (P : (F.centralizerSystem p E).CentricOrbit) :
    L.BLODiagramCentralizerPair p hS sat E ⟨P.obj.as.subgroup, P.property⟩ =
      L.BLOCohomologyCoverPoint p
        ((F.localCentricToCentralizedCover p hS sat E
          (F.akoCentralizerInput p hS sat E)).obj P) := rfl

@[reassoc] theorem BLOCohomologyToRightKan_centralizerPair (n : ℕ)
    (E : F.ElementaryCategory p) (P : (F.centralizerSystem p E).CentricOrbit) :
    (L.BLOCohomologyToRightKan p n).app E ≫
        (V28.rightKanCohomologyLimitIso p F hS sat n E).hom ≫
        limit.π _ (op P) =
      L.BLOCohomologyRestriction (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
        (L.BLODiagramCentralizerPair p hS sat E ⟨P.obj.as.subgroup, P.property⟩) ≫
        OrdinaryCohomology.pull (R := PrimeField.{u} p) (A := PrimeField.{u} p)
          (subgroupAmbientEquiv (F.centralizerGroup p E) P.obj.as.subgroup).toMonoidHom n := by
  exact L.BLOCohomologyToRightKan_centralizerLimit p hS sat n E P

end Sharpness.FusionSystem.CentricLinkingSystem
