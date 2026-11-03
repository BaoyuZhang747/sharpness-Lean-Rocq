(** The concrete universal prefix for a proper image in the evaluation comma. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma CategoryAdjointUniqueness FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices NormalizerPointedChainPrefix LinkingChainRestrictionMaps LinkingChainRestrictionOperations
  NormalizerLinkingChainCategory NormalizerLinkingChainEvaluation
  NormalizerLinkingEvaluationImage NormalizerLinkingEvaluationPrefix NormalizerLinkingEvaluationLift
  NormalizerLinkingEvaluationComponents NormalizerLinkingEvaluationLiftDeletion
  NormalizerLinkingEvaluationDeletionMonic NormalizerLinkingEvaluationMapEquations
  NormalizerLinkingEvaluationPoints NormalizerLinkingEvaluationPrefixData.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerPointedChainPrefix
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionOperations DPNormalizerLinkingChainCategory
  DPNormalizerLinkingChainEvaluation DPNormalizerLinkingEvaluationImage DPNormalizerLinkingEvaluationPrefix
  DPNormalizerLinkingEvaluationLift DPNormalizerLinkingEvaluationComponents
  DPNormalizerLinkingEvaluationLiftDeletion DPNormalizerLinkingEvaluationDeletionMonic
  DPNormalizerLinkingEvaluationMapEquations DPNormalizerLinkingEvaluationPoints
  DPNormalizerLinkingEvaluationPrefixData.

Module DPNormalizerLinkingEvaluationProperImage.
Section ProperImage.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation C := (chain_category L).
Local Notation D := (linking_category L).
Local Notation E := (evaluation L).
Local Notation UC := (evaluation_under L P).
Local Notation PT := (evaluation_points L P).
Local Notation J := (points_inclusion L P).
Variable X : UC.
Let c := costructured_source X.
Let f := costructured_arrow X.
Let I := @image_object S F L P (fobj E c) f.
Let a := @image_isomorphism S F L P (fobj E c) f.
Hypothesis hI : val I \proper val (bottom c).

Definition proper_point : PT := @Build_evaluation_point S F L P (prepend hI)
  (isomorphism_composition a
    (object_equality_iso L (esym (@prepend_entry_zero S F c I hI)))).

Lemma image_inclusion_proper :
  linking_compose L (iso_hom a) (inclusion L (proper_sub hI)) = f.
Proof.
have hi : proper_sub hI = @image_sub S F L P (fobj E c) f := Prop_irrelevance _ _.
rewrite hi; exact: image_isomorphism_inclusion.
Qed.

Definition proper_deletion : hom UC (point_under proper_point) X.
Proof.
refine (@Build_costructured_hom (opposite C) (opposite D) (functor_op E) P
  X (point_under proper_point) (deletion L hI) _).
change (linking_compose L
  (linking_compose L (iso_hom a)
    (iso_hom (object_equality_iso L (esym (@prepend_entry_zero S F c I hI)))))
  (evaluation_arrow (deletion L hI)) = f).
rewrite deletion_evaluation linking_assoc object_chart_cancel.
exact: image_inclusion_proper.
Defined.

Section Lift.
Variable Y : PT.
Variable k : hom UC (point_under Y) X.
Let t := point_chain Y.
Let u : chain_map L t c := costructured_map k.
Let b : @isomorphism D (bottom t) I :=
  isomorphism_composition (iso_symm (point_iso Y)) a.

Lemma lift_first_square :
  linking_compose L (@chain_inclusion S F L t ord0 _
    (leq0n (DPNormalizerChainIndices.index (selected_indices u) ord0)))
    (iso_hom (entry_isomorphism u ord0)) =
  linking_compose L (iso_hom b) (inclusion L (proper_sub hI)).
Proof.
have hh := congr1 (fun z => linking_compose L (iso_inv (point_iso Y)) z)
  (costructured_commutes k).
change (linking_compose L (iso_inv (point_iso Y))
  (linking_compose L (iso_hom (point_iso Y)) (evaluation_arrow u)) =
  linking_compose L (iso_inv (point_iso Y)) f) in hh.
have hi := iso_inv_hom (point_iso Y).
change (linking_compose L (iso_inv (point_iso Y)) (iso_hom (point_iso Y)) =
  linking_identity L (bottom t)) in hi.
rewrite -linking_assoc hi linking_id_left
  -image_inclusion_proper -linking_assoc in hh.
exact hh.
Qed.

Let v := @prefix_lift S F L t c u I hI b lift_first_square.

Definition proper_lift : hom PT Y proper_point.
Proof.
refine (@Build_costructured_hom (opposite C) (opposite D) (functor_op E) P
  (point_under proper_point) (point_under Y) v _).
change (linking_compose L (iso_hom (point_iso Y)) (evaluation_arrow v) =
  linking_compose L (iso_hom a)
    (iso_hom (object_equality_iso L (esym (@prepend_entry_zero S F c I hI))))).
rewrite lift_evaluation.
change (linking_compose L (iso_hom (point_iso Y))
  (linking_compose L (linking_compose L (iso_inv (point_iso Y)) (iso_hom a))
    (iso_hom (object_equality_iso L (esym (@prepend_entry_zero S F c I hI))))) =
  linking_compose L (iso_hom a)
    (iso_hom (object_equality_iso L (esym (@prepend_entry_zero S F c I hI))))).
have hi := iso_hom_inv (point_iso Y).
change (linking_compose L (iso_hom (point_iso Y)) (iso_inv (point_iso Y)) =
  linking_identity L P) in hi.
by rewrite -!linking_assoc hi linking_id_left.
Defined.

Lemma proper_lift_spec :
  @Category.compose UC _ _ _ (fmap J proper_lift) proper_deletion = k.
Proof.
apply costructured_hom_ext.
change (composite_chain_map v (deletion L hI) = u).
exact: lift_deletion.
Qed.

Lemma proper_lift_unique (g : hom PT Y proper_point)
    (hg : @Category.compose UC _ _ _ (fmap J g) proper_deletion = k) : proper_lift = g.
Proof.
apply costructured_hom_ext.
apply (@deletion_monic S F L t c I hI).
have h := f_equal (@costructured_map (opposite C) (opposite D) (functor_op E) P
  X (point_under Y)) hg.
change (composite_chain_map (costructured_map g) (deletion L hI) = u) in h.
change (composite_chain_map v (deletion L hI) =
  composite_chain_map (costructured_map g) (deletion L hI)).
rewrite lift_deletion; exact: esym h.
Qed.
End Lift.

Definition proper_image_data : prefix_data X.
Proof.
refine (@Build_prefix_data S F L P X proper_point proper_deletion _)=> Y k.
exists (proper_lift k); split; [exact: proper_lift_spec | exact: proper_lift_unique].
Defined.
End ProperImage.
End DPNormalizerLinkingEvaluationProperImage.
