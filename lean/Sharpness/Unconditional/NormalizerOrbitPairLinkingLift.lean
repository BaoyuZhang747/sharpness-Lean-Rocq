import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsEmbedding
import Sharpness.Unconditional.NormalizerOrbitExtensionJoins
import Sharpness.Unconditional.NormalizerOrbitPairCategory
import Sharpness.FusionCentricClosure

/-! The actual acting homomorphism of a normalizer pair, and prescribed
linking restrictions compatible with individual normalizing elements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerPairActingHom (A : F.NormalizerOrbitPair) :
    A.centric.obj.as.subgroup →* L.ChainAut A.chain :=
  (L.chainNormalizerToAut A.chain).comp (subgroupInclusion _ _ (by
    intro x hx
    exact (A.chain.mem_normalizerSubgroup x).mpr (fun i => A.normalizes i hx)))

theorem normalizerPairActingHom_component (A : F.NormalizerOrbitPair)
    (x : A.centric.obj.as.subgroup) (i : Fin (A.chain.length+1)) :
    (L.normalizerPairActingHom A x).val i =
      L.normalizerToLinkingAut (A.chain.linkingObject L i) ⟨x.val,A.normalizes i x.property⟩ := rfl

theorem normalizerPair_normalizing_element_square {P Q : L.Object}
    (hPQ : P.as.val ≤ Q.as.val) (x : Q.as.val)
    (hx : x.val ∈ Subgroup.normalizer (P.as.val : Set S)) :
    (L.normalizerToLinkingAut P ⟨x.val,hx⟩).hom ≫ L.inclusionLift hPQ =
      L.inclusionLift hPQ ≫ (L.distinguished Q x).hom := by
  apply L.cancel_right _ _ (L.topInclusionLift Q)
  rw [Category.assoc, L.inclusionLift_comp_top]
  change (L.normalizerAutOverTop P _).hom ≫ _ = _
  rw [L.normalizerAutOverTop_square, Category.assoc, L.commutation,
    ← Category.assoc, L.inclusionLift_comp_top, L.projection_topInclusionLift]
  rfl

theorem normalizerPair_exists_prescribed_restriction {P Q U V : L.Object}
    (hPU : P.as.val ≤ U.as.val) (hQV : Q.as.val ≤ V.as.val)
    (b : U ⟶ V) (e : L.projection.obj P ≅ L.projection.obj Q)
    (he : e.hom ≫ L.projection.map (L.inclusionLift hQV) =
      L.projection.map (L.inclusionLift hPU) ≫ L.projection.map b) :
    ∃ t : P ≅ Q, t.hom ≫ L.inclusionLift hQV = L.inclusionLift hPU ≫ b := by
  let c := L.normalizerLinkingIsoLift e
  have hc : L.projection.map c.hom = e.hom := L.normalizerLinkingIsoLift_projection e
  have hp : L.projection.map (c.hom ≫ L.inclusionLift hQV) =
      L.projection.map (L.inclusionLift hPU ≫ b) := by
    rw [L.projection.map_comp,L.projection.map_comp,hc,he]
  obtain ⟨z,hz,_⟩ := (L.central_fiber (c.hom ≫ L.inclusionLift hQV)
    (L.inclusionLift hPU ≫ b)).mp hp
  exact ⟨(L.distinguished P z.val).trans c, (Category.assoc _ _ _).trans hz⟩

theorem normalizerPair_restriction_intertwines {P Q U V : L.Object}
    (hPU : P.as.val ≤ U.as.val) (hQV : Q.as.val ≤ V.as.val)
    (b : U ⟶ V) (t : P ≅ Q)
    (ht : t.hom ≫ L.inclusionLift hQV = L.inclusionLift hPU ≫ b)
    (x : U.as.val) (hx : x.val ∈ Subgroup.normalizer (P.as.val : Set S))
    (hy : ((L.projection.map b).val x).val ∈ Subgroup.normalizer (Q.as.val : Set S)) :
    (L.normalizerToLinkingAut P ⟨x.val,hx⟩).hom ≫ t.hom =
      t.hom ≫ (L.normalizerToLinkingAut Q ⟨((L.projection.map b).val x).val,hy⟩).hom := by
  apply L.cancel_right _ _ (L.inclusionLift hQV)
  rw [Category.assoc,ht,← Category.assoc,
    L.normalizerPair_normalizing_element_square hPU x hx,Category.assoc,L.commutation,
    ← Category.assoc,← ht,Category.assoc,
    ← L.normalizerPair_normalizing_element_square hQV ((L.projection.map b).val x) hy,
    ← Category.assoc]

end Sharpness.FusionSystem.CentricLinkingSystem
