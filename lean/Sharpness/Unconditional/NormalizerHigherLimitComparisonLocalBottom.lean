import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalConjugation

/-! The actual bottom subgroup embeds normally in the actual linking-chain
automorphism group. The proof uses the chain-preserving top automorphism
and the linking commutation axiom. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricChain
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

def bottomToNormalizer (σ : F.CentricChain) : σ.subgroup 0 →* σ.normalizerSubgroup where
  toFun x := ⟨x.val, (σ.mem_normalizerSubgroup x.val).mpr (fun i =>
    Subgroup.le_normalizer (σ.subgroup_mono (Fin.zero_le i) x.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Sharpness.FusionSystem.CentricChain
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def chainBottomToAut (σ : F.CentricChain) : σ.subgroup 0 →* L.ChainAut σ :=
  (L.chainNormalizerToAut σ).comp σ.bottomToNormalizer

def chainBottomImage (σ : F.CentricChain) : Subgroup (L.ChainAut σ) :=
  (L.chainBottomToAut σ).range

theorem chainBottomToAut_conjugate (σ : F.CentricChain) (g : L.ChainAut σ)
    (x : σ.subgroup 0) :
    ∃ y : σ.subgroup 0, L.chainBottomToAut σ y = g * L.chainBottomToAut σ x * g⁻¹ := by
  let a := L.chainFusionProjection σ g
  let xT : σ.topSubgroup := ⟨x.val, σ.subgroup_mono (Fin.zero_le _) x.property⟩
  let y : σ.subgroup 0 := ⟨(a.val.val xT).val, (a.property 0 xT).mp x.property⟩
  refine ⟨y, ?_⟩
  apply L.chainAutTopProjection_injective σ
  rw [map_mul, map_mul, map_inv]
  let Z := σ.linkingObject L (Fin.last σ.length)
  let nx : Subgroup.normalizer (Z.as.val : Set S) := ⟨x.val, Subgroup.le_normalizer xT.property⟩
  let ny : Subgroup.normalizer (Z.as.val : Set S) :=
    ⟨y.val, Subgroup.le_normalizer (σ.subgroup_mono (Fin.zero_le _) y.property)⟩
  change L.normalizerToLinkingAut Z ny =
    (L.chainAutProjection σ (Fin.last σ.length) g) * L.normalizerToLinkingAut Z nx * _
  rw [L.normalizerToLinkingAut_of_mem Z ny (σ.subgroup_mono (Fin.zero_le _) y.property),
    L.normalizerToLinkingAut_of_mem Z nx xT.property]
  exact (L.linkingAut_conjugates_distinguished _ _ xT).symm

instance chainBottomImage_normal (σ : F.CentricChain) : (L.chainBottomImage σ).Normal where
  conj_mem x hx g := by
    obtain ⟨y, rfl⟩ := hx
    exact L.chainBottomToAut_conjugate σ g y

theorem chainBottomImage_isPGroup (p : ℕ) (hS : IsPGroup p S) (σ : F.CentricChain) :
    IsPGroup p (L.chainBottomImage σ) :=
  (hS.to_subgroup (σ.subgroup 0)).of_surjective
    (L.chainBottomToAut σ).rangeRestrict (L.chainBottomToAut σ).rangeRestrict_surjective

theorem chainBottomImage_le_normalizerRange (σ : F.CentricChain) :
    L.chainBottomImage σ ≤ (L.chainNormalizerToAut σ).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨σ.bottomToNormalizer x, rfl⟩

end Sharpness.FusionSystem.CentricLinkingSystem

