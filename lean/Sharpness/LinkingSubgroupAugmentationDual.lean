import Sharpness.LinkingSubgroupChainAugmentation
import Sharpness.LinkingSubgroupTotalDualEvaluation
import Sharpness.LinkingSubgroupAugmentation
import Sharpness.ZeroColumnTotalProjection

/-! The actual geometric cochain augmentation is exactly the Hom
dual of the constructed actual chain augmentation. Its composite
with the actual Alexander–Whitney cochain comparison is therefore
the dual of the actual diagonal augmentation, as entire cochain maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

theorem subgroupCochainAugmentation_otherColumn (p q n : ℕ) (h : p+q=n) (hp : p≠0) :
    (L.subgroupCochainAugmentation R A).f n ≫
      totalSummandProjectionAt (L.subgroupBicomplex R A) p q n h = 0 := by
  change ((replacementConeColumnMap (L.subgroupCochainDiagram R A)
      (L.subgroupCochainRestrictionCone R A) ⦋0⦌).f n ≫
      (L.subgroupBicomplex R A).ιTotal (ComplexShape.up ℕ) 0 n n (by change 0+n=n; omega)) ≫ _ = _
  rw [Category.assoc,
    totalSummandProjectionAt_other (L.subgroupBicomplex R A) p q n 0 n h (by omega) (by omega), comp_zero]

theorem subgroupCochainAugmentation_totalDual :
    L.subgroupCochainAugmentation R A ≫ (L.subgroupTotalDualCochainIso R A).hom =
      SingularCohomology.chainDualMap R (L.subgroupChainAugmentation R) A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (L.subgroupTotalDualCochainIso R A).hom.f n ((L.subgroupCochainAugmentation R A).f n z) =
    (L.subgroupChainAugmentation R).f n ≫ z
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change p+q=n at h
  apply moduleDirectSum_hom_ext
  intro s
  change (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫
      ((L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h ≫
        (L.subgroupTotalDualCochainIso R A).hom.f n ((L.subgroupCochainAugmentation R A).f n z)) =
    (chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫
      ((L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h ≫
        ((L.subgroupChainAugmentation R).f n ≫ z))
  rw [← Category.assoc, subgroupTotalDualCochainIso_evaluation]
  by_cases hp : p=0
  · subst p
    have hq : q=n := by omega
    subst q
    calc
      _ = ((SingularCohomology.chainsFunctor R).map (L.subgroupDiagramForget (chainHead s))).f n ≫ z :=
        congrArg (fun t => t z)
          (replacementConeAugmentation_projection (L.subgroupCochainDiagram R A)
            (L.subgroupCochainRestrictionCone R A) n s)
      _ = ((chainReplacementInclusion (L.subgroupChainDiagram R) ⦋0⦌ s).f n ≫
          (L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) 0 n n (by change 0+n=n; omega) ≫
          (L.subgroupChainAugmentation R).f n) ≫ z :=
        congrArg (fun t => t ≫ z) (L.subgroupChainAugmentation_zeroColumn R n s).symm
      _ = _ := by simp only [Category.assoc]
  · calc
      _ = 0 := congrArg (fun t => t z s) (L.subgroupCochainAugmentation_otherColumn R A p q n h hp)
      _ = ((chainReplacementInclusion (L.subgroupChainDiagram R) ⦋p⦌ s).f q ≫
          ((L.subgroupChainBicomplex R).ιTotal (ComplexShape.down ℕ) p q n h ≫
            (L.subgroupChainAugmentation R).f n)) ≫ z := by
        rw [subgroupChainAugmentation_otherColumn L R p q n h hp, comp_zero, zero_comp]
      _ = _ := by simp only [Category.assoc]

theorem subgroupCochainAugmentation_alexanderWhitney (ez : EilenbergZilberInput.{u} R) :
    L.subgroupCochainAugmentation R A ≫ L.subgroupAlexanderWhitneyCochainMap R ez A =
      SingularCohomology.chainDualMap R (L.subgroupSingularDiagonalChainMap R) A := by
  change L.subgroupCochainAugmentation R A ≫
      ((L.subgroupTotalDualCochainIso R A).hom ≫
        SingularCohomology.chainDualMap R (L.subgroupAlexanderWhitney R ez) A) = _
  rw [← Category.assoc, subgroupCochainAugmentation_totalDual,
    ← SingularCohomology.chainDualMap_comp, subgroupAlexanderWhitney_chainAugmentation]

theorem subgroupCochainAugmentation_quasiIso_iff_diagonal (ez : EilenbergZilberInput.{u} R) :
    QuasiIso (L.subgroupCochainAugmentation R A) ↔
      QuasiIso (SingularCohomology.chainDualMap R (L.subgroupSingularDiagonalChainMap R) A) := by
  letI := L.subgroupAlexanderWhitneyCochainMap_quasiIso R ez A
  rw [← L.subgroupCochainAugmentation_alexanderWhitney R A ez]
  exact (quasiIso_iff_comp_right
    (L.subgroupCochainAugmentation R A) (L.subgroupAlexanderWhitneyCochainMap R ez A)).symm

theorem subgroupChainAugmentation_quasiIso_iff_diagonal (ez : EilenbergZilberInput.{u} R) :
    QuasiIso (L.subgroupChainAugmentation R) ↔ QuasiIso (L.subgroupSingularDiagonalChainMap R) := by
  letI := L.subgroupAlexanderWhitney_quasiIso R ez
  rw [← L.subgroupAlexanderWhitney_chainAugmentation R ez]
  exact (quasiIso_iff_comp_left (L.subgroupAlexanderWhitney R ez) (L.subgroupChainAugmentation R)).symm

end Sharpness.FusionSystem.CentricLinkingSystem
