(** Literal evaluation of the actual prefix deletion and its constructed lift. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemCancellation LinkingChainObjects
  LinkingChainAutomorphisms NormalizerChainIndices NormalizerPointedChainPrefix
  LinkingChainRestrictionMaps LinkingChainTransportEqualities NormalizerLinkingChainComponents
  NormalizerLinkingChainEvaluation NormalizerLinkingEvaluationPrefix
  NormalizerLinkingEvaluationLift NormalizerLinkingEvaluationComponents.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingCancellation DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPNormalizerPointedChainPrefix DPLinkingChainRestrictionMaps
  DPLinkingChainTransportEqualities DPNormalizerLinkingChainComponents
  DPNormalizerLinkingChainEvaluation DPNormalizerLinkingEvaluationPrefix
  DPNormalizerLinkingEvaluationLift DPNormalizerLinkingEvaluationComponents.

Module DPNormalizerLinkingEvaluationMapEquations.
Section Equations.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Lemma evaluation_entry_zero (c d : chain F) (f : chain_map L c d)
    (h : index (selected_indices f) ord0 = ord0) :
  evaluation_arrow f = @entry_at S F L c d f ord0 ord0 h.
Proof.
have he : @bottom_inclusion S F L c (index (selected_indices f) ord0) =
    iso_hom (@entry_equality_iso S F L c _ _ (esym h)).
  apply (@compose_right_injective S F L _ _ _
    (iso_hom (@entry_equality_iso S F L c _ _ h))).
  by rewrite bottom_inclusion_chart bottom_inclusion_refl entry_chart_inverse.
rewrite /evaluation_arrow /bottom_arrow /entry_at he; reflexivity.
Qed.

Lemma deletion_evaluation (d : chain F) (I : DPFusionOrbit.centric_object F)
    (hI : val I \proper val (bottom d)) :
  evaluation_arrow (deletion L hI) =
  linking_compose L (iso_hom (object_equality_iso L (@prepend_entry_zero S F d I hI)))
    (inclusion L (proper_sub hI)).
Proof.
change (linking_compose L
  (@chain_inclusion S F L (prepend hI) ord0 _ (leq0n (index (deletion_selector hI) ord0)))
  (iso_hom (object_equality_iso L (@deletion_entry_equality S F d I hI ord0))) =
  linking_compose L (iso_hom (object_equality_iso L (@prepend_entry_zero S F d I hI)))
    (inclusion L (proper_sub hI))).
exact: DPNormalizerLinkingEvaluationPrefix.inclusion_equality_square.
Qed.

Variables c d : chain F.
Variable f : chain_map L c d.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom d).
Variable b : @isomorphism (linking_category L) (bottom c) I.
Hypothesis first_square :
  linking_compose L (@chain_inclusion S F L c ord0 _ (leq0n (index (selected_indices f) ord0)))
    (iso_hom (entry_isomorphism f ord0)) =
  linking_compose L (iso_hom b) (inclusion L (proper_sub hI)).

Theorem lift_evaluation :
  evaluation_arrow (@prefix_lift S F L c d f I hI b first_square) =
  linking_compose L (iso_hom b)
    (iso_hom (object_equality_iso L (esym (@prepend_entry_zero S F d I hI)))).
Proof.
rewrite (@evaluation_entry_zero c (prepend hI)
  (@prefix_lift S F L c d f I hI b first_square)
  (@extended_index_zero S F c d I hI (selected_indices f)
    (@selected_bottom_positive S F L c d f I hI b))).
exact: lift_first_entry_at.
Qed.
End Equations.
End DPNormalizerLinkingEvaluationMapEquations.
