import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalFusion
import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalBottom

/-! Compatibility of the ambient centric collection with the actual local
fusion system. Only the valid inclusion is asserted: ambient centric implies
local centric. Bottom containment gives ambient centricity in the other direction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem ambientCentric_of_chainNormalizerIso (p : ℕ) (sat : F.Saturated p)
    (σ : F.CentricChain) {P Q : Subgroup σ.normalizerSubgroup} (e : P ≃* Q)
    (he : (L.chainNormalizerFusion σ).IsHom e.toMonoidHom)
    (hP : F.IsCentric (σ.normalizerAmbientSubgroup P)) :
    F.IsCentric (σ.normalizerAmbientSubgroup Q) := by
  let a := (σ.normalizerAmbientEquiv P).symm.trans (e.trans (σ.normalizerAmbientEquiv Q))
  have ha : F.IsHom a.toMonoidHom :=
    σ.normalizerExtension_allowed _ ((L.chainNormalizerFusion_isHom_iff p sat σ _).mp he)
  exact F.isoSystem.centricIn_of_iso a ha hP

theorem chainNormalizerCentric_of_ambientCentric (p : ℕ) (sat : F.Saturated p)
    (σ : F.CentricChain) (P : Subgroup σ.normalizerSubgroup)
    (hP : F.IsCentric (σ.normalizerAmbientSubgroup P)) :
    (L.chainNormalizerFusion σ).IsCentric P := by
  intro Q _ e he x hx
  have hQ := L.ambientCentric_of_chainNormalizerIso p sat σ e he hP
  have hc : x.val ∈ Subgroup.centralizer (σ.normalizerAmbientSubgroup Q : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro y ⟨z, hz, rfl⟩
    exact congrArg (fun w : σ.normalizerSubgroup => w.val)
      (Subgroup.mem_centralizer_iff.mp hx.1 z hz)
  have hself := hQ (σ.normalizerAmbientSubgroup Q) le_top
    (MulEquiv.refl _) (F.id_mem _)
  have hxQ : x.val ∈ σ.normalizerAmbientSubgroup Q := hself ⟨hc, Subgroup.mem_top _⟩
  obtain ⟨z, hz, heq⟩ := hxQ
  have hzx : z = x := Subtype.ext heq
  exact hzx ▸ hz

theorem ambientCentric_of_chainBottomImage_le (σ : F.CentricChain)
    (P : Subgroup σ.normalizerSubgroup)
    (hP : L.chainBottomImage σ ≤ P.map (L.chainNormalizerToAut σ)) :
    F.IsCentric (σ.normalizerAmbientSubgroup P) := by
  apply F.centric_overgroup (σ.centric 0)
  intro x hx
  have hi : L.chainBottomToAut σ ⟨x, hx⟩ ∈ L.chainBottomImage σ := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨y, hy, he⟩ := hP hi
  have hyx : y = σ.bottomToNormalizer ⟨x, hx⟩ := L.chainNormalizerToAut_injective σ he
  exact ⟨y, hy, congrArg (fun z : σ.normalizerSubgroup => z.val) hyx⟩

end Sharpness.FusionSystem.CentricLinkingSystem
