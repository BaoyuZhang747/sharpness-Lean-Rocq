(** The actual compatible linking ladder obtained by inserting its prescribed
    first image. The new first isomorphism is the supplied factor, and retained
    entries are the original ladder components through explicit equality charts. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices NormalizerPointedChainPrefix LinkingChainRestrictionMaps
  NormalizerLinkingEvaluationPrefix NormalizerLinkingEvaluationCharts
  NormalizerLinkingEvaluationLiftSquares.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPNormalizerPointedChainPrefix DPLinkingChainRestrictionMaps
  DPNormalizerLinkingEvaluationPrefix DPNormalizerLinkingEvaluationCharts
  DPNormalizerLinkingEvaluationLiftSquares.

Module DPNormalizerLinkingEvaluationLift.
Section Lift.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variable f : chain_map L c d.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom d).
Variable b : @isomorphism (linking_category L) (bottom c) I.
Let hp := @selected_bottom_positive S F L c d f I hI b.
Let e := @extended_selector S F c d I hI (selected_indices f) hp.

Definition retained_entry_iso (i : 'I_(length d).+1) :
    @isomorphism (linking_category L)
      (entry c (index e (lift ord0 i))) (entry (prepend hI) (lift ord0 i)) :=
  chart_iso
    (f_equal (entry c) (@extended_index_lift S F c d I hI (selected_indices f) hp i))
    (@prepend_entry_lift S F d I hI i) (entry_isomorphism f i).

Definition first_entry_iso : @isomorphism (linking_category L)
    (entry c (index e ord0)) (entry (prepend hI) ord0) :=
  chart_iso
    (f_equal (entry c) (@extended_index_zero S F c d I hI (selected_indices f) hp))
    (@prepend_entry_zero S F d I hI) b.

Definition lifted_entry_iso (i : 'I_(length d).+2) :
    @isomorphism (linking_category L) (entry c (index e i)) (entry (prepend hI) i).
Proof.
case: (unliftP ord0 i)=> [j ->|->].
- exact (retained_entry_iso j).
- exact first_entry_iso.
Defined.

Lemma lifted_entry_zero : lifted_entry_iso ord0 = first_entry_iso.
Proof.
rewrite /lifted_entry_iso.
case: (unliftP ord0 ord0)=> [j hj|hj].
- have h := congr1 val hj.
  change (0 = (lift ord0 j : nat)) in h; by rewrite lift0 in h.
- have -> : hj = Logic.eq_refl ord0 := Prop_irrelevance _ _; reflexivity.
Qed.

Lemma lifted_entry_lift (i : 'I_(length d).+1) :
  lifted_entry_iso (lift ord0 i) = retained_entry_iso i.
Proof.
rewrite /lifted_entry_iso.
case: (unliftP ord0 (lift ord0 i))=> [j hj|hj].
- have hij : i = j := lift_inj hj.
  case: j / hij in hj *.
  have -> : hj = Logic.eq_refl (lift ord0 i) := Prop_irrelevance _ _; reflexivity.
- have h := congr1 val hj.
  change ((lift ord0 i : nat) = 0) in h; by rewrite lift0 in h.
Qed.

Hypothesis first_square :
  linking_compose L (@chain_inclusion S F L c ord0 _ (leq0n (index (selected_indices f) ord0)))
    (iso_hom (entry_isomorphism f ord0)) =
  linking_compose L (iso_hom b) (inclusion L (proper_sub hI)).

Lemma lifted_entry_square (i j : 'I_(length d).+2) (hij : i <= j) :
  linking_compose L (@chain_inclusion S F L c _ _ (index_mono e hij))
    (iso_hom (lifted_entry_iso j)) =
  linking_compose L (iso_hom (lifted_entry_iso i))
    (@chain_inclusion S F L (prepend hI) i j hij).
Proof.
case: (unliftP ord0 i) hij=> [i' ->|->] hij;
  case: (unliftP ord0 j) hij=> [j' ->|->] hij.
- have hij' : i' <= j' by move: hij; rewrite !lift0 /=.
  rewrite !lifted_entry_lift /retained_entry_iso.
  apply: (@chart_iso_square S F L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (@entry_mono S F c _ _ (@index_mono S F c d (selected_indices f) i' j' hij'))
    (@entry_mono S F d i' j' hij')).
  exact (@entry_square S F L c d f i' j' hij').
- have hh : (lift ord0 i' : nat) <= 0 := hij.
  by rewrite lift0 in hh.
- rewrite lifted_entry_zero lifted_entry_lift /first_entry_iso /retained_entry_iso.
  apply: (@chart_iso_square S F L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (@entry_mono S F c ord0 _ (leq0n (index (selected_indices f) j')))
    (@prefix_sub_entry S F d I (proper_sub hI) j')).
  exact (@prefix_entry_square S F L c d f I (proper_sub hI) b first_square j').
- have he : @index_mono S F c (prepend hI) e ord0 ord0 hij = leqnn (index e ord0) :=
    Prop_irrelevance _ _.
  have hj : hij = leqnn (ord0 : 'I_(length d).+2) := Prop_irrelevance _ _.
  rewrite he hj !chain_inclusion_refl linking_id_left linking_id_right; reflexivity.
Qed.

Definition prefix_lift : chain_map L c (prepend hI) :=
  @Build_chain_map S F L c (prepend hI) e lifted_entry_iso lifted_entry_square.

Lemma prefix_lift_indices : selected_indices prefix_lift = e.
Proof. reflexivity. Qed.
End Lift.
End DPNormalizerLinkingEvaluationLift.
