(** Literal component normalization for the image-prefix deletion and lift. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryAdjointUniqueness FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices NormalizerPointedChainPrefix LinkingChainRestrictionMaps
  LinkingChainTransportEqualities NormalizerLinkingChainComponents
  NormalizerLinkingEvaluationPrefix NormalizerLinkingEvaluationCharts NormalizerLinkingEvaluationLift.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndices
  DPNormalizerPointedChainPrefix DPLinkingChainRestrictionMaps DPLinkingChainTransportEqualities
  DPNormalizerLinkingChainComponents DPNormalizerLinkingEvaluationPrefix
  DPNormalizerLinkingEvaluationCharts DPNormalizerLinkingEvaluationLift.

Module DPNormalizerLinkingEvaluationComponents.
Section Components.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Lemma object_chart_comp (P Q R : Obj) (h : P = Q) (k : Q = R) :
  linking_compose L (iso_hom (object_equality_iso L h)) (iso_hom (object_equality_iso L k)) =
  iso_hom (object_equality_iso L (eq_trans h k)).
Proof. case: Q / h in k *; case: R / k; exact: linking_id_left. Qed.

Lemma object_chart_loop (P : Obj) (h : P = P) :
  iso_hom (object_equality_iso L h) = linking_identity L P.
Proof. have -> : h = Logic.eq_refl P := Prop_irrelevance _ _; reflexivity. Qed.

Lemma object_chart_inverse (P Q : Obj) (h : P = Q) :
  linking_compose L (iso_hom (object_equality_iso L (esym h)))
    (iso_hom (object_equality_iso L h)) = linking_identity L Q.
Proof. case: Q / h; exact: linking_id_left. Qed.

Lemma object_chart_cancel (P Q R : Obj) (h : P = Q) (k : Q = P)
    (a : linking_hom L P R) :
  linking_compose L (iso_hom (object_equality_iso L h))
    (linking_compose L (iso_hom (object_equality_iso L k)) a) = a.
Proof.
case: Q / h in k *.
have -> : k = Logic.eq_refl P := Prop_irrelevance _ _.
change (linking_compose L (linking_identity L P)
  (linking_compose L (linking_identity L P) a) = a).
by rewrite !linking_id_left.
Qed.

Lemma index_chart_object (c : chain F) (i j : 'I_(length c).+1) (h : i = j) :
  iso_hom (@entry_equality_iso S F L c i j h) =
  iso_hom (object_equality_iso L (f_equal (entry c) h)).
Proof. case: j / h; reflexivity. Qed.

Lemma deletion_entry_at (d : chain F) (I : Obj) (hI : val I \proper val (bottom d))
    (i : 'I_(length d).+1) :
  @entry_at S F L (prepend hI) d (deletion L hI) i (lift ord0 i) (deletion_index hI i) =
  iso_hom (object_equality_iso L (@prepend_entry_lift S F d I hI i)).
Proof.
rewrite /entry_at index_chart_object /deletion /deletion_entry_iso /= object_chart_comp.
congr (iso_hom (object_equality_iso L _)); exact: Prop_irrelevance.
Qed.

Variables c d : chain F.
Variable f : chain_map L c d.
Variable I : Obj.
Hypothesis hI : val I \proper val (bottom d).
Variable b : @isomorphism (linking_category L) (bottom c) I.
Hypothesis first_square :
  linking_compose L (@chain_inclusion S F L c ord0 _ (leq0n (index (selected_indices f) ord0)))
    (iso_hom (entry_isomorphism f ord0)) =
  linking_compose L (iso_hom b) (inclusion L (proper_sub hI)).
Let hp := @selected_bottom_positive S F L c d f I hI b.
Let e := @extended_selector S F c d I hI (selected_indices f) hp.
Let g := @prefix_lift S F L c d f I hI b first_square.

Lemma lift_retained_entry_at (i : 'I_(length d).+1) :
  @entry_at S F L c (prepend hI) g (lift ord0 i) (index (selected_indices f) i)
    (@extended_index_lift S F c d I hI (selected_indices f) hp i) =
  linking_compose L (iso_hom (entry_isomorphism f i))
    (iso_hom (object_equality_iso L (esym (@prepend_entry_lift S F d I hI i)))).
Proof.
rewrite /entry_at index_chart_object.
change (linking_compose L
  (iso_hom (object_equality_iso L (f_equal (entry c)
    (esym (@extended_index_lift S F c d I hI (selected_indices f) hp i)))))
  (iso_hom (@lifted_entry_iso S F L c d f I hI b (lift ord0 i))) =
  linking_compose L (iso_hom (entry_isomorphism f i))
    (iso_hom (object_equality_iso L (esym (@prepend_entry_lift S F d I hI i))))).
rewrite lifted_entry_lift /retained_entry_iso /chart_iso /isomorphism_composition /=.
exact: object_chart_cancel.
Qed.

Lemma lift_first_entry_at :
  @entry_at S F L c (prepend hI) g ord0 ord0 (@extended_index_zero S F c d I hI (selected_indices f) hp) =
  linking_compose L (iso_hom b)
    (iso_hom (object_equality_iso L (esym (@prepend_entry_zero S F d I hI)))).
Proof.
rewrite /entry_at index_chart_object.
change (linking_compose L
  (iso_hom (object_equality_iso L (f_equal (entry c)
    (esym (@extended_index_zero S F c d I hI (selected_indices f) hp)))))
  (iso_hom (@lifted_entry_iso S F L c d f I hI b ord0)) =
  linking_compose L (iso_hom b)
    (iso_hom (object_equality_iso L (esym (@prepend_entry_zero S F d I hI))))).
rewrite lifted_entry_zero /first_entry_iso /chart_iso /isomorphism_composition /=.
exact: object_chart_cancel.
Qed.
End Components.
End DPNormalizerLinkingEvaluationComponents.
