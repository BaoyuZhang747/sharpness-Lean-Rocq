import Sharpness.Unconditional.NormalizerOrbitPairLinkingLift

/-! A simultaneous normalizer extension has a prescribed linking ladder.
Its actual acting subgroup actions intertwine on every selected entry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem normalizerPair_exists_linkingLift {A B : F.NormalizerOrbitPair}
    (f : A.centric.obj.as ⟶ B.centric.obj.as)
    (a : F.NormalizerChainExtension A.chain B.chain f) :
    ∃ t : L.normalizerSubdivisionObj A.chain ⟶ L.normalizerSubdivisionObj B.chain,
      t.indices = a.indices ∧ ∀ x : A.centric.obj.as.subgroup,
        L.normalizerSubdivisionAutHom A.chain (L.normalizerPairActingHom A x) ≫ t =
          t ≫ L.normalizerSubdivisionAutHom B.chain (L.normalizerPairActingHom B (f.val x)) := by
  let U : L.Object := ⟨⟨A.centric.obj.as.subgroup ⊔
    A.chain.subgroup (a.indices (Fin.last B.chain.length)),
    F.centric_overgroup A.centric.property le_sup_left⟩⟩
  let V : L.Object := ⟨⟨B.centric.obj.as.subgroup ⊔ B.chain.topSubgroup,
    F.centric_overgroup B.centric.property le_sup_left⟩⟩
  have hU (i : Fin (B.chain.length+1)) : A.chain.subgroup (a.indices i) ≤ U.as.val :=
    (A.chain.subgroup_mono (a.indices.monotone (Fin.le_last i))).trans le_sup_right
  have hV (i : Fin (B.chain.length+1)) : B.chain.subgroup i ≤ V.as.val :=
    (B.chain.subgroup_mono (Fin.le_last i)).trans le_sup_right
  obtain ⟨b,hb⟩ := L.projection_surjective U V a.joinHom
  have hc (i : Fin (B.chain.length+1)) :
      ∃ c : A.chain.linkingObject L (a.indices i) ≅ B.chain.linkingObject L i,
        c.hom ≫ L.inclusionLift (hV i) = L.inclusionLift (hU i) ≫ b := by
    let ei := F.restrictRawIso
      (A.chain.subgroup_mono (a.indices.monotone (Fin.le_last i)))
      (B.chain.subgroup_mono (Fin.le_last i)) a.chainIso (a.chainConjugacy.maps i)
    apply L.normalizerPair_exists_prescribed_restriction (hU i) (hV i) b ei
    rw [L.projection_inclusionLift,L.projection_inclusionLift,hb]
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rfl
  choose c hc using hc
  have hcomp (i j : Fin (B.chain.length+1)) (hij : i ≤ j) :
      (c i).hom ≫ L.chainInclusion B.chain hij =
        L.chainInclusion A.chain (a.indices.monotone hij) ≫ (c j).hom := by
    apply L.cancel_right _ _ (L.inclusionLift (hV j))
    change ((c i).hom ≫ L.inclusionLift _) ≫ _ = (L.inclusionLift _ ≫ (c j).hom) ≫ _
    rw [Category.assoc,L.inclusionLift_comp,hc i,Category.assoc,hc j,
      ← Category.assoc,L.inclusionLift_comp]
  let t : L.normalizerSubdivisionObj A.chain ⟶ L.normalizerSubdivisionObj B.chain :=
    { indices := a.indices, component := c, commutes := hcomp }
  refine ⟨t,rfl,?_⟩
  intro x
  apply NormalizerSubdivisionHom.ext
  · rfl
  apply heq_of_eq
  funext i
  apply Iso.ext
  let xU : U.as.val := ⟨x.val,Subgroup.mem_sup_left x.property⟩
  have hyval : ((L.projection.map b).val xU).val = (f.val x).val := by
    rw [hb]
    exact a.joinHom_onActing x
  have hy : ((L.projection.map b).val xU).val ∈
      Subgroup.normalizer (B.chain.subgroup i : Set S) := by
    rw [hyval]
    exact B.normalizes i (f.val x).property
  have h := L.normalizerPair_restriction_intertwines (hU i) (hV i) b (c i) (hc i)
    xU (A.normalizes (a.indices i) x.property) hy
  have hye : (⟨((L.projection.map b).val xU).val,hy⟩ :
      Subgroup.normalizer (B.chain.subgroup i : Set S)) =
        ⟨(f.val x).val,B.normalizes i (f.val x).property⟩ := Subtype.ext hyval
  rw [hye] at h
  exact h

def normalizerPairLinkingLift {A B : F.NormalizerOrbitPair}
    (f : A.centric.obj.as ⟶ B.centric.obj.as)
    (a : F.NormalizerChainExtension A.chain B.chain f) :
    L.normalizerSubdivisionObj A.chain ⟶ L.normalizerSubdivisionObj B.chain :=
  Classical.choose (L.normalizerPair_exists_linkingLift f a)

theorem normalizerPairLinkingLift_indices {A B : F.NormalizerOrbitPair}
    (f : A.centric.obj.as ⟶ B.centric.obj.as)
    (a : F.NormalizerChainExtension A.chain B.chain f) :
    (L.normalizerPairLinkingLift f a).indices = a.indices :=
  (Classical.choose_spec (L.normalizerPair_exists_linkingLift f a)).1

theorem normalizerPairLinkingLift_intertwines {A B : F.NormalizerOrbitPair}
    (f : A.centric.obj.as ⟶ B.centric.obj.as)
    (a : F.NormalizerChainExtension A.chain B.chain f) (x : A.centric.obj.as.subgroup) :
    L.normalizerSubdivisionAutHom A.chain (L.normalizerPairActingHom A x) ≫
        L.normalizerPairLinkingLift f a = L.normalizerPairLinkingLift f a ≫
      L.normalizerSubdivisionAutHom B.chain (L.normalizerPairActingHom B (f.val x)) :=
  (Classical.choose_spec (L.normalizerPair_exists_linkingLift f a)).2 x

end Sharpness.FusionSystem.CentricLinkingSystem
