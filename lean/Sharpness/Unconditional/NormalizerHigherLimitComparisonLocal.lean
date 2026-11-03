import Sharpness.Unconditional.LinkingNormalizerRestriction
import Sharpness.FusionCentricClosure

/-! The local chain normalizer morphisms are actual extensions over the join
with the top subgroup, preserving all entries of the chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricChain
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

/-- An ambient subgroup map extends over the chain top, with a genuine
fusion automorphism of that top preserving each chain entry. -/
def NormalizerExtension (σ : F.CentricChain) {P Q : Subgroup S} (f : P →* Q) : Prop :=
  ∃ a : σ.fusionStabilizer, ∃ b : (σ.topSubgroup ⊔ P : Subgroup S) →* (σ.topSubgroup ⊔ Q : Subgroup S),
    F.IsHom b ∧
    (∀ x : σ.topSubgroup, (b ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (a.val.val x).val) ∧
    (∀ x : P, (b ⟨x.val, Subgroup.mem_sup_right x.property⟩).val = (f x).val)

omit [Finite S] in
theorem normalizerJoin_le_normalizer (σ : F.CentricChain) {P : Subgroup S}
    (hP : P ≤ σ.normalizerSubgroup) :
    σ.topSubgroup ⊔ P ≤ Subgroup.normalizer (σ.topSubgroup : Set S) :=
  sup_le Subgroup.le_normalizer (fun _ hx =>
    (σ.mem_normalizerSubgroup _).mp (hP hx) (Fin.last σ.length))

end Sharpness.FusionSystem.CentricChain
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerJoinObject (σ : F.CentricChain) (P : Subgroup S) : L.Object :=
  ⟨⟨σ.topSubgroup ⊔ P, F.centric_overgroup
    (σ.centric (Fin.last σ.length)) le_sup_left⟩⟩

/-- Every actual extension induces conjugation by an actual compatible
chain tuple, with equality on each element of its source subgroup. -/
theorem normalizerExtension_induced_by_chainAut (σ : F.CentricChain)
    {P Q : Subgroup S} (hP : P ≤ σ.normalizerSubgroup) (hQ : Q ≤ σ.normalizerSubgroup)
    (f : P →* Q) (hf : σ.NormalizerExtension f) :
    ∃ g : L.ChainAut σ, ∀ x : P,
      L.chainNormalizerToAut σ ⟨(f x).val, hQ (f x).property⟩ =
        g * L.chainNormalizerToAut σ ⟨x.val, hP x.property⟩ * g⁻¹ := by
  obtain ⟨a, b, hb, htop, hf⟩ := hf
  let Z := σ.linkingObject L (Fin.last σ.length)
  let U := L.normalizerJoinObject σ P
  let V := L.normalizerJoinObject σ Q
  have hZU : Z.as.val ≤ U.as.val := le_sup_left
  have hZV : Z.as.val ≤ V.as.val := le_sup_left
  have hUN : U.as.val ≤ Subgroup.normalizer (Z.as.val : Set S) :=
    σ.normalizerJoin_le_normalizer hP
  have hVN : V.as.val ≤ Subgroup.normalizer (Z.as.val : Set S) :=
    σ.normalizerJoin_le_normalizer hQ
  obtain ⟨t, ht⟩ := L.projection_surjective U V ⟨b, hb⟩
  have hrestrict : L.projection.map (L.inclusionLift hZU ≫ t) =
      (F.isoOfMulEquiv a.val.val a.val.property).hom ≫ F.inclusion hZV := by
    rw [L.projection.map_comp, L.projection_inclusionLift, ht]
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact htop x
  obtain ⟨c, hc, hsquare⟩ := L.exists_linking_normalizer_restriction hZU hZV a.val t hrestrict
  have hcK : c ∈ L.chainTopStabilizer σ := by
    change L.linkingAutProjection Z c ∈ σ.fusionStabilizer
    rw [hc]
    exact a.property
  obtain ⟨g, hg⟩ := L.exists_chainAut_with_top σ c hcK
  refine ⟨g, fun x => ?_⟩
  apply L.chainAutTopProjection_injective σ
  rw [map_mul, map_mul, map_inv, hg]
  have he := L.linking_normalizer_extension_conjugation hZU hZV hUN hVN c t hsquare
    (⟨x.val, Subgroup.mem_sup_right x.property⟩ : U.as.val)
  have hval : ((L.projection.map t).val ⟨x.val, Subgroup.mem_sup_right x.property⟩).val = (f x).val := by
    rw [ht]
    exact hf x
  have hh : L.normalizerToLinkingAut Z
      ⟨((L.projection.map t).val ⟨x.val, Subgroup.mem_sup_right x.property⟩).val,
        hVN ((L.projection.map t).val ⟨x.val, Subgroup.mem_sup_right x.property⟩).property⟩ =
      L.normalizerToLinkingAut Z
        ⟨(f x).val, (σ.mem_normalizerSubgroup _).mp (hQ (f x).property) (Fin.last σ.length)⟩ :=
    congrArg (L.normalizerToLinkingAut Z) (Subtype.ext hval)
  exact hh.symm.trans he

end Sharpness.FusionSystem.CentricLinkingSystem


