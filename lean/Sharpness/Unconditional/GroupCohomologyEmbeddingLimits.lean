import Sharpness.Unconditional.GroupCohomologyEmbeddingStable
import Sharpness.Unconditional.FiniteGroupCohomologyCentricLimit

/-! Native centric limits for fusion induced along an actual injective
embedding. The inverse comparison has literal restriction at every object. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory CategoryTheory.Limits Opposite
variable {R G T A : Type u} [CommRing R] [Group G] [Finite G]
    [Group T] [Finite T] [AddCommGroup A] [Module R A]
    (i : T →* G) (hi : Function.Injective i)
    (p : ℕ) [Fact p.Prime] (hT : IsPGroup p T)
    (sat : (finiteGroupFusionAlong i hi).Saturated p)
    (hindex : IsUnit (i.range.index : R)) (n : ℕ)

def embeddingCentricLimitIso :
    limit ((finiteGroupFusionAlong i hi).cohomologyCoefficient (R := R) (A := A) n) ≅
      value R G A n :=
  HasLimit.isoOfNatIso ((finiteGroupFusionAlong i hi).nativeCohomologyMackeyCentricIso n).symm ≪≫
    (finiteGroupFusionAlong i hi).nativeCentricStableIso
      ((finiteGroupFusionAlong i hi).alperinInput p hT sat)
      ((finiteGroupFusionAlong i hi).nativeGroupCohomologyMackey n) ≪≫
    (finiteGroupFusionAlongCohomologyStableIso i hi n hindex).symm

def embeddingCentricHigherLimitZeroIso :
    higherLimit ((finiteGroupFusionAlong i hi).cohomologyCoefficient
      (R := R) (A := A) n) 0 ≅ value R G A n :=
  higherLimitIso ((finiteGroupFusionAlong i hi).nativeCohomologyMackeyCentricIso n).symm 0 ≪≫
    (((finiteGroupFusionAlong i hi).coefficientData
      ((finiteGroupFusionAlong i hi).nativeGroupCohomologyMackey (R := R) (A := A) n)).onFull
        (finiteGroupFusionAlong i hi).centricProperty).higherLimitZeroIso ≪≫
    ((finiteGroupFusionAlong i hi).compatibleStableLinearEquiv
      ((finiteGroupFusionAlong i hi).alperinInput p hT sat)
      ((finiteGroupFusionAlong i hi).nativeGroupCohomologyMackey n)).toModuleIso ≪≫
    (finiteGroupFusionAlongCohomologyStableIso i hi n hindex).symm

theorem embeddingCentricLimitIso_hom_pull :
    (embeddingCentricLimitIso (R := R) (A := A) i hi p hT sat hindex n).hom ≫
      pull (i.comp (⊤ : Subgroup T).subtype) n =
        limit.π ((finiteGroupFusionAlong i hi).cohomologyCoefficient (R := R) (A := A) n)
          (op ⟨(finiteGroupFusionAlong i hi).topOrbit, (finiteGroupFusionAlong i hi).top_centric⟩) := by
  simp only [embeddingCentricLimitIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← finiteGroupFusionAlongCohomologyStableIso_hom_subtype i hi n hindex,
    Iso.inv_hom_id_assoc, FusionSystem.nativeCentricStableIso_evaluation,
    HasLimit.isoOfNatIso_hom_π]
  rfl

theorem embeddingCentricLimitIso_inv_top :
    (embeddingCentricLimitIso (R := R) (A := A) i hi p hT sat hindex n).inv ≫
        limit.π ((finiteGroupFusionAlong i hi).cohomologyCoefficient (R := R) (A := A) n)
          (op ⟨(finiteGroupFusionAlong i hi).topOrbit, (finiteGroupFusionAlong i hi).top_centric⟩) =
      pull (i.comp (⊤ : Subgroup T).subtype) n := by
  rw [← embeddingCentricLimitIso_hom_pull i hi p hT sat hindex n, Iso.inv_hom_id_assoc]

theorem embeddingCentricLimitIso_inv_component
    (P : (finiteGroupFusionAlong i hi).CentricOrbit) :
    (embeddingCentricLimitIso (R := R) (A := A) i hi p hT sat hindex n).inv ≫
        limit.π ((finiteGroupFusionAlong i hi).cohomologyCoefficient (R := R) (A := A) n) (op P) =
      pull (i.comp P.obj.as.subgroup.subtype) n := by
  let F := finiteGroupFusionAlong i hi
  let D := F.cohomologyCoefficient (R := R) (A := A) n
  let a : P ⟶ (⟨F.topOrbit, F.top_centric⟩ : F.CentricOrbit) := ⟨F.toTop P.obj⟩
  have hmap : D.map a.op = pull (R := R) (A := A)
      (F.inclusion (show P.obj.as.subgroup ≤ ⊤ from le_top)).val n :=
    F.cohomologyOrbitCoefficient_map_raw n (F.inclusion le_top)
  rw [← limit.w D a.op, ← Category.assoc, embeddingCentricLimitIso_inv_top,
    hmap, ← pull_comp]
  rfl

end Sharpness.OrdinaryCohomology

