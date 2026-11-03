import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsNormalizer
import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsKernel
import Sharpness.Unconditional.FusionAtomicCentric

/-! The actual simultaneous subgroup normalizer embeds in the compatible
linking-chain group. Its image is exactly the inverse image of the
K-normalizer automizer, proved using the actual maps and finite orders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def chainNormalizerCoordinate (σ : F.CentricChain) (s : σ.normalizerSubgroup)
    (i : Fin (σ.length + 1)) : Aut (σ.linkingObject L i) :=
  L.normalizerToLinkingAut (σ.linkingObject L i)
    ⟨s.val, (σ.mem_normalizerSubgroup s.val).mp s.property i⟩

theorem chainNormalizerCoordinate_square (σ : F.CentricChain) (s : σ.normalizerSubgroup)
    (i : Fin (σ.length + 1)) :
    (L.chainNormalizerCoordinate σ s i).hom ≫ L.topInclusionLift (σ.linkingObject L i) =
      L.topInclusionLift (σ.linkingObject L i) ≫ (L.topDistinguished s.val).hom :=
  L.normalizerAutOverTop_square _ _

theorem chainNormalizerCoordinate_compatible (σ : F.CentricChain) (s : σ.normalizerSubgroup) :
    L.ChainCompatible σ (L.chainNormalizerCoordinate σ s) := by
  intro i j hij
  apply L.cancel_right _ _ (L.topInclusionLift (σ.linkingObject L j))
  change ((L.chainNormalizerCoordinate σ s i).hom ≫ L.inclusionLift _) ≫ _ =
    (L.inclusionLift _ ≫ (L.chainNormalizerCoordinate σ s j).hom) ≫ _
  rw [Category.assoc, L.inclusionLift_comp_top, L.chainNormalizerCoordinate_square,
    Category.assoc, L.chainNormalizerCoordinate_square, ← Category.assoc,
    L.inclusionLift_comp_top]

/-- The distinguished action of the actual simultaneous subgroup normalizer. -/
def chainNormalizerToAut (σ : F.CentricChain) : σ.normalizerSubgroup →* L.ChainAut σ where
  toFun s := ⟨L.chainNormalizerCoordinate σ s, L.chainNormalizerCoordinate_compatible σ s⟩
  map_one' := by
    apply Subtype.ext
    funext i
    exact map_one (L.normalizerToLinkingAut (σ.linkingObject L i))
  map_mul' s t := by
    apply Subtype.ext
    funext i
    exact map_mul (L.normalizerToLinkingAut (σ.linkingObject L i))
      ⟨s.val, (σ.mem_normalizerSubgroup s.val).mp s.property i⟩
      ⟨t.val, (σ.mem_normalizerSubgroup t.val).mp t.property i⟩

theorem chainNormalizerToAut_injective (σ : F.CentricChain) :
    Function.Injective (L.chainNormalizerToAut σ) := by
  intro s t h
  have h0 := congrArg (fun a : L.ChainAut σ => a.val 0) h
  have he := L.normalizerToLinkingAut_injective (σ.linkingObject L 0) h0
  apply Subtype.ext
  exact congrArg (fun x : Subgroup.normalizer (σ.subgroup 0 : Set S) => x.val) he

def chainNormalizerKEquiv (σ : F.CentricChain) :
    σ.normalizerSubgroup ≃* F.kNormalizer σ.topSubgroup σ.fusionStabilizer :=
  MulEquiv.subgroupCongr σ.normalizerSubgroup_eq_kNormalizer

theorem chainNormalizerToAut_projection (σ : F.CentricChain) (s : σ.normalizerSubgroup) :
    L.chainFusionProjection σ (L.chainNormalizerToAut σ s) =
      F.kNormalizerToAut σ.topSubgroup σ.fusionStabilizer ((chainNormalizerKEquiv (F := F) σ) s) := by
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact congrArg (fun a : F.automorphismSubgroup σ.topSubgroup => a.val x)
    (L.normalizerToLinkingAut_projection (σ.linkingObject L (Fin.last σ.length))
      ⟨s.val, (σ.mem_normalizerSubgroup s.val).mp s.property (Fin.last σ.length)⟩)

theorem chainNormalizer_card (σ : F.CentricChain) :
    Nat.card σ.normalizerSubgroup = Nat.card (Subgroup.center σ.topSubgroup) *
      Nat.card (F.kNormalizerToAut σ.topSubgroup σ.fusionStabilizer).range := by
  rw [Nat.card_congr ((chainNormalizerKEquiv (F := F) σ)).toEquiv, F.kNormalizer_card]
  congr 1
  have hcent : Subgroup.centralizer (σ.topSubgroup : Set S) ≤ σ.topSubgroup := by
    have h := σ.centric (Fin.last σ.length) σ.topSubgroup le_top
      (MulEquiv.refl σ.topSubgroup) (F.id_mem σ.topSubgroup)
    simpa only [inf_top_eq] using h
  exact (Nat.card_congr (centerEquivAmbientCentralizer σ.topSubgroup hcent).toEquiv).symm

end Sharpness.FusionSystem.CentricLinkingSystem
