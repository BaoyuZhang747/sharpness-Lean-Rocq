import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsKernel

/-! The finite Sylow subgroup obtained by lifting the actual chain
K-normalizer automizer across the proved normal p-kernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def chainNormalizerSylowCandidate (σ : F.CentricChain) : Subgroup (L.ChainAut σ) :=
  (F.kNormalizerToAut σ.topSubgroup σ.fusionStabilizer).range.comap
    (L.chainFusionProjection σ)

theorem chainNormalizerSylowCandidate_isPGroup (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (σ : F.CentricChain) :
    IsPGroup p (L.chainNormalizerSylowCandidate σ) :=
  (F.kNormalizerToAut_range_isPGroup p hS σ.topSubgroup σ.fusionStabilizer).comap_of_ker_isPGroup
    (L.chainFusionProjection σ) (L.chainFusionProjection_kernel_isPGroup p hS σ)

theorem chainNormalizerSylowCandidate_index (σ : F.CentricChain) :
    (L.chainNormalizerSylowCandidate σ).index =
      (F.kNormalizerToAut σ.topSubgroup σ.fusionStabilizer).range.index :=
  Subgroup.index_comap_of_surjective _ (L.chainFusionProjection_surjective σ)

/-- Full K-normalization is the existing concrete cardinal maximality
condition, not an assumed saturation or Sylow conclusion for a new subsystem. -/
def chainNormalizerSylow (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S)
    (sat : F.Saturated p) (σ : F.CentricChain)
    (hσ : F.FullyKNormalized σ.topSubgroup σ.fusionStabilizer) : Sylow p (L.ChainAut σ) :=
  (L.chainNormalizerSylowCandidate_isPGroup p hS σ).toSylow (by
    rw [L.chainNormalizerSylowCandidate_index]
    exact (F.fullyKNormalized_properties p hS sat _ _ hσ).2)

theorem chainNormalizerSylow_coe (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S)
    (sat : F.Saturated p) (σ : F.CentricChain)
    (hσ : F.FullyKNormalized σ.topSubgroup σ.fusionStabilizer) :
    (L.chainNormalizerSylow p hS sat σ hσ : Subgroup (L.ChainAut σ)) =
      L.chainNormalizerSylowCandidate σ := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
