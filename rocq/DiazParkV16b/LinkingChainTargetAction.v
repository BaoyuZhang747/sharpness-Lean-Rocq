(** The genuine compatible target-automorphism action on linking-chain
    maps. This is the algebra behind the projection-comma reflection. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryAdjointUniqueness FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainIndices
  CategoryAutomorphismConjugation LinkingChainRestrictionMaps LinkingChainTransportEqualities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPLinkingChainRestrictionMaps DPLinkingChainTransportEqualities
  DPCategoryAutomorphismConjugation.
Local Open Scope group_scope.

Module DPLinkingChainTargetAction.
Section Action.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variable f : chain_map L c d.
Variable a : chain_automorphism_group L d.

Definition target_entry_iso i := isomorphism_composition (entry_isomorphism f i)
  (automorphism_isomorphism (@projection S F L d i a)).

Lemma target_entry_square (i j : 'I_(length d).+1) (hij : i <= j) :
    linking_compose L (@chain_inclusion S F L c _ _ (index_mono (selected_indices f) hij))
      (iso_hom (target_entry_iso j)) =
    linking_compose L (iso_hom (target_entry_iso i)) (@chain_inclusion S F L d i j hij).
Proof.
change (linking_compose L (@chain_inclusion S F L c _ _ (index_mono (selected_indices f) hij))
  (linking_compose L (iso_hom (entry_isomorphism f j)) (@projection S F L d j a)) =
  linking_compose L (linking_compose L (iso_hom (entry_isomorphism f i)) (@projection S F L d i a))
    (@chain_inclusion S F L d i j hij)).
rewrite -linking_assoc (entry_square f hij) !linking_assoc.
rewrite -(projection_square a hij); reflexivity.
Qed.

Definition target_action : chain_map L c d :=
  @Build_chain_map S F L c d (selected_indices f) target_entry_iso target_entry_square.

Lemma target_action_selection : selected_indices target_action = selected_indices f.
Proof. reflexivity. Qed.

Lemma target_action_component i : iso_hom (entry_isomorphism target_action i) =
    linking_compose L (iso_hom (entry_isomorphism f i)) (@projection S F L d i a).
Proof. reflexivity. Qed.
End Action.

Section Faithfulness.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variable f : chain_map L c d.

Theorem target_action_component_faithful (a b : chain_automorphism_group L d)
    (h : forall i, iso_hom (entry_isomorphism (target_action f a) i) =
      iso_hom (entry_isomorphism (target_action f b) i)) : a = b.
Proof.
apply projection_ext=> i.
apply (@iso_cancel_left (linking_category L) _ _ _ (entry_isomorphism f i)).
exact (h i).
Qed.
End Faithfulness.
End DPLinkingChainTargetAction.
