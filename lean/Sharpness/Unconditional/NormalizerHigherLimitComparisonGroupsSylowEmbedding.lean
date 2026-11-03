import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsEmbedding
import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsSylow

/-! The image of the actual simultaneous subgroup normalizer is exactly
the Sylow preimage constructed from the K-normalizer automizer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.NormalizerReflection
variable {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] [Finite H] in
theorem subgroupComap_card (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  let g := f.subgroupComap K
  calc
    Nat.card (K.comap f) = Nat.card ((K.comap f) ⧸ g.ker) * Nat.card g.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
    _ = Nat.card K * Nat.card f.ker := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g
        (f.subgroupComap_surjective_of_surjective K hf)).toEquiv,
        Nat.card_congr (subgroupComapKernelEquiv f K).toEquiv]

end Sharpness.NormalizerReflection

namespace Sharpness.FusionSystem.CentricLinkingSystem
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem chainNormalizerToAut_range_le (σ : F.CentricChain) :
    (L.chainNormalizerToAut σ).range ≤ L.chainNormalizerSylowCandidate σ := by
  rintro _ ⟨s, rfl⟩
  exact ⟨chainNormalizerKEquiv σ s, (L.chainNormalizerToAut_projection σ s).symm⟩

theorem chainNormalizerSylowCandidate_card (σ : F.CentricChain) :
    Nat.card (L.chainNormalizerSylowCandidate σ) = Nat.card σ.normalizerSubgroup := by
  rw [chainNormalizer_card σ]
  change Nat.card ((F.kNormalizerToAut σ.topSubgroup σ.fusionStabilizer).range.comap
    (L.chainFusionProjection σ)) = _
  rw [NormalizerReflection.subgroupComap_card _ (L.chainFusionProjection_surjective σ),
    ← Nat.card_congr (L.chainFusionCenterKernelEquiv σ).toEquiv, mul_comm]

/-- The canonical normalizer homomorphism has exactly the intended image. -/
theorem chainNormalizerToAut_range (σ : F.CentricChain) :
    (L.chainNormalizerToAut σ).range = L.chainNormalizerSylowCandidate σ := by
  apply Subgroup.eq_of_le_of_card_ge (L.chainNormalizerToAut_range_le σ)
  rw [L.chainNormalizerSylowCandidate_card]
  exact (Nat.card_congr (MonoidHom.ofInjective (L.chainNormalizerToAut_injective σ)).toEquiv).le

/-- The literal normalizer is a Sylow subgroup of the literal chain-automorphism
group whenever the chain top/stabilizer pair is fully K-normalized. -/
theorem chainNormalizerToAut_range_eq_sylow (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain)
    (hσ : F.FullyKNormalized σ.topSubgroup σ.fusionStabilizer) :
    (L.chainNormalizerToAut σ).range =
      (L.chainNormalizerSylow p hS sat σ hσ : Subgroup (L.ChainAut σ)) :=
  L.chainNormalizerToAut_range σ

def chainNormalizerSylowEquiv (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain)
    (hσ : F.FullyKNormalized σ.topSubgroup σ.fusionStabilizer) :
    σ.normalizerSubgroup ≃* (L.chainNormalizerSylow p hS sat σ hσ) :=
  (MonoidHom.ofInjective (L.chainNormalizerToAut_injective σ)).trans
    (MulEquiv.subgroupCongr (L.chainNormalizerToAut_range_eq_sylow p hS sat σ hσ))

end Sharpness.FusionSystem.CentricLinkingSystem
