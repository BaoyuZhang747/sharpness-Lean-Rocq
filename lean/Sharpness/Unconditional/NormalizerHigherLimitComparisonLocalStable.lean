import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalZero
import Sharpness.Unconditional.FusionNormalEmbeddingExtension
import Sharpness.Unconditional.CollectionStableElementsExtension

/-! Direct, map-normalized stable-elements comparison on the ambient
centric normalizer collection. The normal bottom subgroup provides the
actual extension domain for every local fusion morphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (σ : F.CentricChain)

theorem normalizerAmbientCollection_top :
    (L.normalizerAmbientCollection p hS sat σ).member (⊤ : Subgroup σ.normalizerSubgroup) := by
  apply L.ambientCentric_of_chainBottomImage_le σ
  rintro _ ⟨x, rfl⟩
  exact ⟨σ.bottomToNormalizer x, Subgroup.mem_top _, rfl⟩

theorem normalizerAmbientCollection_extension_toTop
    (P : (L.chainNormalizerFusion σ).Object)
    (f : P ⟶ (⟨⊤⟩ : (L.chainNormalizerFusion σ).Object)) :
    ∃ Q : Subgroup σ.normalizerSubgroup,
      (L.normalizerAmbientCollection p hS sat σ).member Q ∧
      ∃ hPQ : P.subgroup ≤ Q,
        ∃ g : (⟨Q⟩ : (L.chainNormalizerFusion σ).Object) ⟶ ⟨⊤⟩,
          (L.chainNormalizerFusion σ).inclusion hPQ ≫ g = f := by
  obtain ⟨g, hg⟩ := (finiteGroupFusionAlong_isHom_iff
    (L.chainNormalizerToAut σ) (L.chainNormalizerToAut_injective σ) f.val).mp f.property
  let t : P.subgroup →* σ.normalizerSubgroup := (⊤ : Subgroup σ.normalizerSubgroup).subtype.comp f.val
  obtain ⟨Q, hPQ, hOQ, b, hb, hbf⟩ := embedding_conjugation_extends_over_normal
    (L.chainNormalizerToAut σ) (L.chainNormalizerToAut_injective σ)
    (L.chainBottomImage σ) (L.chainBottomImage_le_normalizerRange σ) P.subgroup t g hg
  let c : Q →* (⊤ : Subgroup σ.normalizerSubgroup) :=
    Subgroup.topEquiv.symm.toMonoidHom.comp b
  have hc : (L.chainNormalizerFusion σ).IsHom c :=
    (finiteGroupFusionAlong_isHom_iff _ _ c).mpr ⟨g, hb⟩
  refine ⟨Q, L.ambientCentric_of_chainBottomImage_le σ Q hOQ, hPQ, ⟨c, hc⟩, ?_⟩
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  exact hbf x

def normalizerCollectionCompatibleStableIso
    (M : MackeyModule.{u,u,u} R (L.chainNormalizerFusion σ).Orbit
      (L.chainNormalizerFusion σ).mackeyShape) :
    ModuleCat.of R (((L.chainNormalizerFusion σ).coefficientData M).onFull
      (fun P => (L.normalizerAmbientCollection p hS sat σ).member P.as.subgroup)).limit ≅
      ModuleCat.of R ((L.chainNormalizerFusion σ).stableElements M) :=
  ((L.chainNormalizerFusion σ).collectionCompatibleStableLinearEquiv
    (fun P => (L.normalizerAmbientCollection p hS sat σ).member P.as.subgroup)
    (L.normalizerAmbientCollection_top p hS sat σ)
    (L.normalizerAmbientCollection_extension_toTop p hS sat σ) M).toModuleIso

def normalizerCollectionNativeStableIso
    (M : MackeyModule.{u,u,u} R (L.chainNormalizerFusion σ).Orbit
      (L.chainNormalizerFusion σ).mackeyShape) :
    limit ((L.normalizerAmbientCollection p hS sat σ).toCentric.op ⋙
      (L.chainNormalizerFusion σ).centricCoefficient M) ≅
        ModuleCat.of R ((L.chainNormalizerFusion σ).stableElements M) :=
  (((L.chainNormalizerFusion σ).coefficientData M).onFull
    (fun P => (L.normalizerAmbientCollection p hS sat σ).member P.as.subgroup)).nativeLimitCompatibleIso ≪≫
  L.normalizerCollectionCompatibleStableIso p hS sat σ M

theorem normalizerCollectionNativeStableIso_evaluation
    (M : MackeyModule.{u,u,u} R (L.chainNormalizerFusion σ).Orbit
      (L.chainNormalizerFusion σ).mackeyShape) :
    (L.normalizerCollectionNativeStableIso p hS sat σ M).hom ≫
      ModuleCat.ofHom ((L.chainNormalizerFusion σ).stableElements M).subtype =
        limit.π ((L.normalizerAmbientCollection p hS sat σ).toCentric.op ⋙
          (L.chainNormalizerFusion σ).centricCoefficient M)
          (op ⟨(L.chainNormalizerFusion σ).topOrbit, L.normalizerAmbientCollection_top p hS sat σ⟩) := rfl

def normalizerCollectionOrdinaryStableIso (n : ℕ) :
    limit (L.normalizerLocalCohomologyCoefficient (R := R) (A := A) p hS sat σ n) ≅
      ModuleCat.of R ((L.chainNormalizerFusion σ).stableElements
        ((L.chainNormalizerFusion σ).nativeGroupCohomologyMackey (R := R) (A := A) n)) :=
  HasLimit.isoOfNatIso (Functor.isoWhiskerLeft
    (L.normalizerAmbientCollection p hS sat σ).toCentric.op
    ((L.chainNormalizerFusion σ).nativeCohomologyMackeyCentricIso n).symm) ≪≫
  L.normalizerCollectionNativeStableIso p hS sat σ
    ((L.chainNormalizerFusion σ).nativeGroupCohomologyMackey n)

theorem normalizerCollectionOrdinaryStableIso_evaluation (n : ℕ) :
    (L.normalizerCollectionOrdinaryStableIso (R := R) (A := A) p hS sat σ n).hom ≫
      ModuleCat.ofHom ((L.chainNormalizerFusion σ).stableElements
        ((L.chainNormalizerFusion σ).nativeGroupCohomologyMackey (R := R) (A := A) n)).subtype =
      limit.π (L.normalizerLocalCohomologyCoefficient (R := R) (A := A) p hS sat σ n)
        (op ⟨(L.chainNormalizerFusion σ).topOrbit, L.normalizerAmbientCollection_top p hS sat σ⟩) := by
  simp only [normalizerCollectionOrdinaryStableIso, Iso.trans_hom, Category.assoc]
  rw [L.normalizerCollectionNativeStableIso_evaluation, HasLimit.isoOfNatIso_hom_π]
  rfl

end Sharpness.FusionSystem.CentricLinkingSystem

