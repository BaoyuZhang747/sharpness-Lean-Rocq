(** Actual chain composition commutes with target automorphisms, and
    transports source automorphisms by the genuine restriction homomorphism. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryAdjointUniqueness FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainIndices
  CategoryAutomorphismConjugation LinkingChainRestrictionMaps LinkingChainRestrictionOperations
  LinkingChainTargetAction LinkingChainAutomorphismMaps NormalizerLinkingChainExt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations
  DPLinkingChainTargetAction DPLinkingChainAutomorphismMaps DPNormalizerLinkingChainExt
  DPCategoryAutomorphismConjugation.
Local Open Scope group_scope.

Module DPLinkingChainTargetComposition.
Section Composition.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d t : chain F.
Variable f : chain_map L c d.
Variable g : chain_map L d t.

Theorem composite_target_action (a : chain_automorphism_group L t) :
    composite_chain_map f (target_action g a) = target_action (composite_chain_map f g) a.
Proof.
apply chain_map_ext_same=> i.
rewrite /composite_entry_iso /target_entry_iso /isomorphism_composition /=.
rewrite !linking_assoc; reflexivity.
Qed.

Theorem composite_source_action (a : chain_automorphism_group L d) :
    composite_chain_map (target_action f a) g =
    target_action (composite_chain_map f g) (restriction_morphism g a).
Proof.
apply chain_map_ext_same=> i.
rewrite /composite_entry_iso /target_entry_iso /isomorphism_composition /=.
rewrite !linking_assoc.
rewrite restriction_morphism_component.
have hi := @conjugate_intertwines (linking_category L) _ _ (entry_isomorphism g i)
  (@projection S F L d (index (selected_indices g) i) a).
change (linking_compose L (iso_hom (entry_isomorphism g i))
  (conjugate (entry_isomorphism g i) (@projection S F L d (index (selected_indices g) i) a)) =
  linking_compose L (@projection S F L d (index (selected_indices g) i) a)
    (iso_hom (entry_isomorphism g i))) in hi.
rewrite hi; reflexivity.
Qed.
End Composition.
End DPLinkingChainTargetComposition.
