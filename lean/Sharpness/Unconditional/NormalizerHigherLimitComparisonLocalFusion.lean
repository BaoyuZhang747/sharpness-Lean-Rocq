import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalImages
import Sharpness.Unconditional.FusionSystemGroupTransportFinite

/-! The local chain normalizer fusion system is the actual group-induced
system on the actual simultaneous normalizer. Its maps have exactly the
ambient-extension interpretation, and its saturation is proved at the
constructed Sylow representatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricChain
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

abbrev normalizerAmbientSubgroup (σ : F.CentricChain) (P : Subgroup σ.normalizerSubgroup) :
    Subgroup S := P.map σ.normalizerSubgroup.subtype

def normalizerAmbientEquiv (σ : F.CentricChain) (P : Subgroup σ.normalizerSubgroup) :
    P ≃* σ.normalizerAmbientSubgroup P :=
  P.equivMapOfInjective σ.normalizerSubgroup.subtype Subtype.val_injective

theorem normalizerAmbientSubgroup_le (σ : F.CentricChain) (P : Subgroup σ.normalizerSubgroup) :
    σ.normalizerAmbientSubgroup P ≤ σ.normalizerSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  exact x.property

def normalizerAmbientHom (σ : F.CentricChain) {P Q : Subgroup σ.normalizerSubgroup}
    (f : P →* Q) : σ.normalizerAmbientSubgroup P →* σ.normalizerAmbientSubgroup Q :=
  (σ.normalizerAmbientEquiv Q).toMonoidHom.comp
    (f.comp (σ.normalizerAmbientEquiv P).symm.toMonoidHom)

@[simp] theorem normalizerAmbientHom_apply (σ : F.CentricChain)
    {P Q : Subgroup σ.normalizerSubgroup} (f : P →* Q) (x : P) :
    σ.normalizerAmbientHom f (σ.normalizerAmbientEquiv P x) = σ.normalizerAmbientEquiv Q (f x) := by
  simp only [normalizerAmbientHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

end Sharpness.FusionSystem.CentricChain
namespace Sharpness.FusionSystem.CentricLinkingSystem
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

/-- The genuine local fusion system; its embedding is the distinguished action. -/
def chainNormalizerFusion (σ : F.CentricChain) : FusionSystem σ.normalizerSubgroup :=
  finiteGroupFusionAlong (L.chainNormalizerToAut σ) (L.chainNormalizerToAut_injective σ)

/-- All its morphisms are precisely the ambient fusion extensions preserving
the chain, including subgroups which are not ambient centric. -/
theorem chainNormalizerFusion_isHom_iff (p : ℕ) (sat : F.Saturated p)
    (σ : F.CentricChain) {P Q : Subgroup σ.normalizerSubgroup} (f : P →* Q) :
    (L.chainNormalizerFusion σ).IsHom f ↔
      σ.NormalizerExtension (σ.normalizerAmbientHom f) := by
  rw [L.normalizerExtension_iff_chainAut p sat σ
    (σ.normalizerAmbientSubgroup_le P) (σ.normalizerAmbientSubgroup_le Q)]
  change (finiteGroupFusionAlong (L.chainNormalizerToAut σ)
    (L.chainNormalizerToAut_injective σ)).IsHom f ↔ _
  rw [finiteGroupFusionAlong_isHom_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := (σ.normalizerAmbientEquiv P).surjective x
    rw [σ.normalizerAmbientHom_apply]
    exact hg y
  · rintro ⟨g, hg⟩
    refine ⟨g, fun x => ?_⟩
    have h := hg (σ.normalizerAmbientEquiv P x)
    rw [σ.normalizerAmbientHom_apply] at h
    exact h

theorem chainNormalizerFusion_isHom_iff_images (p : ℕ) (sat : F.Saturated p)
    (σ : F.CentricChain) {P Q : Subgroup σ.normalizerSubgroup} (f : P →* Q) :
    (L.chainNormalizerFusion σ).IsHom f ↔
      σ.NormalizerExtensionImages (σ.normalizerAmbientHom f) :=
  (L.chainNormalizerFusion_isHom_iff p sat σ f).trans (σ.normalizerExtension_iff_images _)

theorem chainNormalizerFusion_saturated (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain)
    (hσ : F.FullyKNormalized σ.topSubgroup σ.fusionStabilizer) :
    (L.chainNormalizerFusion σ).Saturated p :=
  finiteGroupFusionAlong_saturated p (L.chainNormalizerToAut σ)
    (L.chainNormalizerToAut_injective σ) (L.chainNormalizerSylow p hS sat σ hσ)
    (L.chainNormalizerToAut_range_eq_sylow p hS sat σ hσ)

theorem normalizerRepresentativeFusion_saturated (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (d : F.NormalizerCategory) :
    (L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).Saturated p :=
  finiteGroupFusionAlong_saturated p _ (L.chainNormalizerToAut_injective _)
    (L.normalizerRepresentativeSylow p hS sat d)
    (L.normalizerRepresentativeSylow_range p hS sat d).symm

end Sharpness.FusionSystem.CentricLinkingSystem
