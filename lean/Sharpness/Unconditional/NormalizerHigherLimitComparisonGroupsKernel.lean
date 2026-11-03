import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsStabilizer

/-! Exact chain-automorphism projection onto the fusion chain stabilizer,
with the actual center kernel and the resulting finite order formula. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.NormalizerReflection
variable {G H : Type u} [Group G] [Group H]

/-- Restricting the codomain to a subgroup leaves the same kernel. -/
def subgroupComapKernelEquiv (f : G →* H) (K : Subgroup H) :
    (f.subgroupComap K).ker ≃* f.ker where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, by
    change f x.val ∈ K
    rw [show f x.val = 1 from x.property]
    exact K.one_mem⟩, Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Sharpness.NormalizerReflection

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def chainTopFusionProjection (σ : F.CentricChain) :
    L.chainTopStabilizer σ →* σ.fusionStabilizer :=
  (L.linkingAutProjection (σ.linkingObject L (Fin.last σ.length))).subgroupComap σ.fusionStabilizer

theorem chainTopFusionProjection_surjective (σ : F.CentricChain) :
    Function.Surjective (L.chainTopFusionProjection σ) :=
  MonoidHom.subgroupComap_surjective_of_surjective _ _ (L.linkingAutProjection_surjective _)

/-- The projection is induced by the actual top coordinate and linking projection. -/
def chainFusionProjection (σ : F.CentricChain) : L.ChainAut σ →* σ.fusionStabilizer :=
  (L.chainTopFusionProjection σ).comp (L.chainAutTopStabilizerEquiv σ).toMonoidHom

theorem chainFusionProjection_surjective (σ : F.CentricChain) :
    Function.Surjective (L.chainFusionProjection σ) :=
  (L.chainTopFusionProjection_surjective σ).comp (L.chainAutTopStabilizerEquiv σ).surjective

theorem chainFusionProjection_apply (σ : F.CentricChain) (a : L.ChainAut σ)
    (x : σ.topSubgroup) :
    (L.chainFusionProjection σ a).val.val x =
      (L.projection.map (a.val (Fin.last σ.length)).hom).val x := rfl

/-- The actual kernel is isomorphic to the subgroup center; no centrality
of its image in the full chain-automorphism group is asserted. -/
def chainFusionCenterKernelEquiv (σ : F.CentricChain) :
    Subgroup.center σ.topSubgroup ≃* (L.chainFusionProjection σ).ker :=
  (L.linkingCenterKernelEquiv (σ.linkingObject L (Fin.last σ.length))).trans
    ((NormalizerReflection.subgroupComapKernelEquiv
      (L.linkingAutProjection (σ.linkingObject L (Fin.last σ.length))) σ.fusionStabilizer).symm.trans
      (((L.chainAutTopStabilizerEquiv σ).symm.subgroupMap (L.chainTopFusionProjection σ).ker).trans
        (MulEquiv.subgroupCongr (MonoidHom.ker_comp_mulEquiv
          (L.chainTopFusionProjection σ) (L.chainAutTopStabilizerEquiv σ)).symm)))

theorem chainFusionProjection_kernel_isPGroup (p : ℕ) (hS : IsPGroup p S)
    (σ : F.CentricChain) : IsPGroup p (L.chainFusionProjection σ).ker :=
  ((hS.to_subgroup σ.topSubgroup).to_subgroup (Subgroup.center σ.topSubgroup)).of_equiv
    (L.chainFusionCenterKernelEquiv σ)

theorem chainAut_card (σ : F.CentricChain) :
    Nat.card (L.ChainAut σ) = Nat.card (Subgroup.center σ.topSubgroup) *
      Nat.card σ.fusionStabilizer := by
  let f := L.chainFusionProjection σ
  calc
    Nat.card (L.ChainAut σ) = Nat.card ((L.ChainAut σ) ⧸ f.ker) * Nat.card f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    _ = Nat.card σ.fusionStabilizer * Nat.card (Subgroup.center σ.topSubgroup) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
        (L.chainFusionProjection_surjective σ)).toEquiv,
        ← Nat.card_congr (L.chainFusionCenterKernelEquiv σ).toEquiv]
    _ = _ := mul_comm _ _

end Sharpness.FusionSystem.CentricLinkingSystem
