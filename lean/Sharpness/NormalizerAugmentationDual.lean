import Sharpness.NormalizerChainAugmentation
import Sharpness.NormalizerTotalDualEvaluation
import Sharpness.NormalizerGeometryBase
import Sharpness.ZeroColumnTotalProjection

/-! The actual geometric cochain augmentation is exactly the Hom
dual of the constructed actual chain augmentation. Its composite
with the actual Alexander–Whitney cochain comparison is therefore
the dual of the actual diagonal augmentation, as entire cochain maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

theorem normalizerCochainAugmentation_otherColumn (p q n : ℕ) (h : p+q=n) (hp : p≠0) :
    (I.normalizerCochainAugmentation R A).f n ≫
      totalSummandProjectionAt (I.normalizerBicomplex R A) p q n h = 0 := by
  change ((replacementConeColumnMap (I.normalizerCochainDiagram R A)
      (I.normalizerCochainRestrictionCone R A) ⦋0⦌).f n ≫
      (I.normalizerBicomplex R A).ιTotal (ComplexShape.up ℕ) 0 n n (by change 0+n=n; omega)) ≫ _ = _
  rw [Category.assoc,
    totalSummandProjectionAt_other (I.normalizerBicomplex R A) p q n 0 n h (by omega) (by omega), comp_zero]

theorem normalizerCochainAugmentation_totalDual :
    I.normalizerCochainAugmentation R A ≫ (I.normalizerTotalDualCochainIso R A).hom =
      SingularCohomology.chainDualMap R (I.normalizerChainAugmentation R) A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (I.normalizerTotalDualCochainIso R A).hom.f n ((I.normalizerCochainAugmentation R A).f n z) =
    (I.normalizerChainAugmentation R).f n ≫ z
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change p+q=n at h
  apply moduleDirectSum_hom_ext
  intro s
  change (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫
      ((I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h ≫
        (I.normalizerTotalDualCochainIso R A).hom.f n ((I.normalizerCochainAugmentation R A).f n z)) =
    (chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫
      ((I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h ≫
        ((I.normalizerChainAugmentation R).f n ≫ z))
  rw [← Category.assoc, normalizerTotalDualCochainIso_evaluation]
  by_cases hp : p=0
  · subst p
    have hq : q=n := by omega
    subst q
    calc
      _ = ((SingularCohomology.chainsFunctor R).map (I.normalizerDiagramForget (chainHead s))).f n ≫ z :=
        congrArg (fun t => t z)
          (replacementConeAugmentation_projection (I.normalizerCochainDiagram R A)
            (I.normalizerCochainRestrictionCone R A) n s)
      _ = ((chainReplacementInclusion (I.normalizerChainDiagram R) ⦋0⦌ s).f n ≫
          (I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) 0 n n (by change 0+n=n; omega) ≫
          (I.normalizerChainAugmentation R).f n) ≫ z :=
        congrArg (fun t => t ≫ z) (I.normalizerChainAugmentation_zeroColumn R n s).symm
      _ = _ := by simp only [Category.assoc]
  · calc
      _ = 0 := congrArg (fun t => t z s) (I.normalizerCochainAugmentation_otherColumn R A p q n h hp)
      _ = ((chainReplacementInclusion (I.normalizerChainDiagram R) ⦋p⦌ s).f q ≫
          ((I.normalizerChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h ≫
            (I.normalizerChainAugmentation R).f n)) ≫ z := by
        rw [normalizerChainAugmentation_otherColumn I R p q n h hp, comp_zero, zero_comp]
      _ = _ := by simp only [Category.assoc]

theorem normalizerCochainAugmentation_alexanderWhitney (ez : EilenbergZilberInput.{u} R) :
    I.normalizerCochainAugmentation R A ≫ I.normalizerAlexanderWhitneyCochainMap R ez A =
      SingularCohomology.chainDualMap R (I.normalizerSingularDiagonalChainMap R) A := by
  change I.normalizerCochainAugmentation R A ≫
      ((I.normalizerTotalDualCochainIso R A).hom ≫
        SingularCohomology.chainDualMap R (I.normalizerAlexanderWhitney R ez) A) = _
  rw [← Category.assoc, normalizerCochainAugmentation_totalDual,
    ← SingularCohomology.chainDualMap_comp, normalizerAlexanderWhitney_chainAugmentation]

theorem normalizerCochainAugmentation_quasiIso_iff_diagonal (ez : EilenbergZilberInput.{u} R) :
    QuasiIso (I.normalizerCochainAugmentation R A) ↔
      QuasiIso (SingularCohomology.chainDualMap R (I.normalizerSingularDiagonalChainMap R) A) := by
  letI := I.normalizerAlexanderWhitneyCochainMap_quasiIso R ez A
  rw [← I.normalizerCochainAugmentation_alexanderWhitney R A ez]
  exact (quasiIso_iff_comp_right
    (I.normalizerCochainAugmentation R A) (I.normalizerAlexanderWhitneyCochainMap R ez A)).symm

theorem normalizerChainAugmentation_quasiIso_iff_diagonal (ez : EilenbergZilberInput.{u} R) :
    QuasiIso (I.normalizerChainAugmentation R) ↔ QuasiIso (I.normalizerSingularDiagonalChainMap R) := by
  letI := I.normalizerAlexanderWhitney_quasiIso R ez
  rw [← I.normalizerAlexanderWhitney_chainAugmentation R ez]
  exact (quasiIso_iff_comp_left (I.normalizerAlexanderWhitney R ez) (I.normalizerChainAugmentation R)).symm

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
