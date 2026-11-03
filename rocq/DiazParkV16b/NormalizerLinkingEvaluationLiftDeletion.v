(** The constructed linking-chain prefix lift composes with literal deletion
    to the original ladder, as an equality of actual chain maps. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices NormalizerPointedChainPrefix LinkingChainRestrictionMaps
  LinkingChainRestrictionOperations NormalizerLinkingChainComponents
  NormalizerLinkingEvaluationPrefix NormalizerLinkingEvaluationLift
  NormalizerLinkingEvaluationComponents.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndices
  DPNormalizerPointedChainPrefix DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations
  DPNormalizerLinkingChainComponents DPNormalizerLinkingEvaluationPrefix
  DPNormalizerLinkingEvaluationLift DPNormalizerLinkingEvaluationComponents.

Module DPNormalizerLinkingEvaluationLiftDeletion.
Section Deletion.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variable f : chain_map L c d.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom d).
Variable b : @isomorphism (linking_category L) (bottom c) I.
Hypothesis first_square :
  linking_compose L (@chain_inclusion S F L c ord0 _ (leq0n (index (selected_indices f) ord0)))
    (iso_hom (entry_isomorphism f ord0)) =
  linking_compose L (iso_hom b) (inclusion L (proper_sub hI)).
Let hp := @selected_bottom_positive S F L c d f I hI b.
Let g := @prefix_lift S F L c d f I hI b first_square.
Let delta := deletion L hI.

Lemma lift_deletion_index (i : 'I_(length d).+1) :
  index (selected_indices (composite_chain_map g delta)) i = index (selected_indices f) i.
Proof.
change (index (DPNormalizerChainIndices.compose (selected_indices g) (selected_indices delta)) i =
  index (selected_indices f) i).
rewrite compose_index.
change (index (@extended_selector S F c d I hI (selected_indices f) hp)
  (index (deletion_selector hI) i) = index (selected_indices f) i).
rewrite deletion_index; exact: extended_index_lift.
Qed.

Theorem lift_deletion : composite_chain_map g delta = f.
Proof.
apply (@chain_map_ext_at S F L c d (composite_chain_map g delta) f
  (fun i => index (selected_indices f) i) lift_deletion_index (fun i => Logic.eq_refl _))=> i.
rewrite (@composite_entry_at S F L c (prepend hI) d g delta i (lift ord0 i)
  (index (selected_indices f) i) (deletion_index hI i)
  (@extended_index_lift S F c d I hI (selected_indices f) hp i) (lift_deletion_index i)).
rewrite lift_retained_entry_at deletion_entry_at entry_at_refl.
by rewrite linking_assoc object_chart_inverse linking_id_right.
Qed.
End Deletion.
End DPNormalizerLinkingEvaluationLiftDeletion.
