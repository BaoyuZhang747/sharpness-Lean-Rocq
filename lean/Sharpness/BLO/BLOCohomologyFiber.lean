import Sharpness.BLO.BLOCohomologyCover

/-! Every fiber and centralizer-limit projection of the canonical comparison.
These formulas identify the actual maps, before proving invertibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)

@[reassoc] theorem BLOCohomologyToRightKan_fiber (n : ℕ) (E : F.ElementaryCategory p)
    (X : Fiber (F.centralizerCoverFibration p) E) :
    (L.BLOCohomologyToRightKan p n).app E ≫
        (V28.rightKanCohomologyFiberIso p F sat n E).hom ≫ limit.π _ X =
      (L.BLOCohomologyDiagram p n).map (eqToHom X.property.symm) ≫
        (L.BLOCohomologyCoverRestriction p n).app X.val := by
  rw [V28.rightKanCohomologyFiberIso_hom_projection]
  rw [← Category.assoc, ← (L.BLOCohomologyToRightKan p n).naturality]
  rw [Category.assoc, L.BLOCohomologyToRightKan_counit_app]

@[reassoc] theorem BLOCohomologyToRightKan_restrictionLimit (n : ℕ)
    (E : F.ElementaryCategory p) (P : (F.centralizerSystem p E).CentricOrbit) :
    (L.BLOCohomologyToRightKan p n).app E ≫
        (V28.rightKanCohomologyRestrictionLimitIso p F hS sat n E).hom ≫
        limit.π _ (op P) =
      (L.BLOCohomologyCoverRestriction p n).app
        (op ((F.localCentricToCentralizedCover p hS sat E
          (F.akoCentralizerInput p hS sat E)).obj P)) := by
  simp only [V28.rightKanCohomologyRestrictionLimitIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Functor.Initial.limitIso_inv]
  change (L.BLOCohomologyToRightKan p n).app E ≫
      (V28.rightKanCohomologyFiberIso p F sat n E).hom ≫
      limit.pre (Fiber.fiberInclusion ⋙ V28.centralizerCoverCohomology p F n)
        (F.centralizerCoverFibrationFiberEquivalence p hS sat E
          (F.akoCentralizerInput p hS sat E)).functor ≫
      limit.π ((F.centralizerCoverFibrationFiberEquivalence p hS sat E
          (F.akoCentralizerInput p hS sat E)).functor ⋙
        Fiber.fiberInclusion ⋙ V28.centralizerCoverCohomology p F n) (op P) = _
  rw [limit.pre_π]
  rw [L.BLOCohomologyToRightKan_fiber p sat]
  change (L.BLOCohomologyDiagram p n).map (𝟙 E) ≫ _ = _
  rw [(L.BLOCohomologyDiagram p n).map_id E, Category.id_comp]
  rfl

@[reassoc] theorem BLOCohomologyToRightKan_centralizerLimit (n : ℕ)
    (E : F.ElementaryCategory p) (P : (F.centralizerSystem p E).CentricOrbit) :
    (L.BLOCohomologyToRightKan p n).app E ≫
        (V28.rightKanCohomologyLimitIso p F hS sat n E).hom ≫
        limit.π _ (op P) =
      (L.BLOCohomologyCoverRestriction p n).app
        (op ((F.localCentricToCentralizedCover p hS sat E
          (F.akoCentralizerInput p hS sat E)).obj P)) ≫
        OrdinaryCohomology.pull (R := PrimeField.{u} p) (A := PrimeField.{u} p)
          (subgroupAmbientEquiv (F.centralizerGroup p E) P.obj.as.subgroup).toMonoidHom n := by
  simp only [V28.rightKanCohomologyLimitIso, Iso.trans_hom, Category.assoc,
    HasLimit.isoOfNatIso_hom_π]
  simpa only [Category.assoc, V28.centralizerCohomologyCoefficientIso_hom_app] using congrArg
    (fun t => t ≫ (V28.centralizerCohomologyCoefficientIso p F hS sat n E).hom.app (op P))
    (L.BLOCohomologyToRightKan_restrictionLimit p hS sat n E P)

end Sharpness.FusionSystem.CentricLinkingSystem
