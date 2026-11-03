(** Every centric radical subgroup of fusion induced through a faithful
    embedding contains each ambient normal p-subgroup in the embedded source. *)
From mathcomp Require Import all_boot all_fingroup pgroup nilpotent sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms
  FusionOuterAutomorphisms FusionRadical FusionCentricCriterion.
From DiazParkV16b Require Import FiniteGroupFusionEmbedding FiniteGroupFusionEmbeddingImage
  FiniteGroupFusionEmbeddingAutomorphisms FiniteGroupFusionEmbeddingRadicalGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFiniteGroupFusionEmbeddingImage
  DPFiniteGroupFusionEmbeddingAutomorphisms DPFiniteGroupFusionEmbeddingRadicalGrowth.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingRadical.
Section Radical.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.
Variable p : nat.
Hypothesis pN : p.-group [set: N].
Variable O : {group G}.
Hypothesis nO : O <| [set: G].
Hypothesis pO : p.-group O.
Hypothesis sOT : O \subset image_group E.
Variable P : {group N}.
Local Notation F := (DPFiniteGroupFusionEmbedding.system E).
Local Notation AP := (ambient E P).

Definition normalizer_intersection : {group G} := ('N(AP) :&: O)%G.
Definition normalizer_action_image : {group {perm N}} :=
  ((normalizer_morphism injE P) @* normalizer_intersection)%G.

Lemma normalizer_intersection_normal : normalizer_intersection <| 'N(AP).
Proof. exact: normalGI (subsetT 'N(AP)) nO. Qed.

Lemma normalizer_action_image_normal :
  normalizer_action_image <| DPFusionSaturation.aut_group F P.
Proof.
have h := morphim_normal (normalizer_morphism injE P) normalizer_intersection_normal.
by rewrite normalizer_image in h.
Qed.

Lemma normalizer_action_image_pgroup : p.-group normalizer_action_image.
Proof.
apply: morphim_pgroup; exact: pgroupS (subsetIr 'N(AP) O) pO.
Qed.

Lemma normalizer_action_image_inner : DPFusionRadical.radical F p P ->
  normalizer_action_image \subset DPFusionOuter.inner P.
Proof.
move=> hr; exact: DPFusionRadical.radical_normal_p_sub_inner
  hr normalizer_action_image_pgroup normalizer_action_image_normal.
Qed.

Lemma source_preimage_normal : from_ambient E O <| [set: N].
Proof.
apply/andP; split; first exact: subsetT.
have h := morphpre_norms E (normal_norm nO).
by rewrite morphpreT in h.
Qed.

Lemma normalizer_intersection_contained :
  DPFusionSystem.centric F P -> DPFusionRadical.radical F p P ->
  'N(P) :&: from_ambient E O \subset P.
Proof.
move=> hc hr; apply/subsetP=> n /setIP[hn /morphpreP[_ hon]].
have hEn : E n \in 'N(AP).
  have h := ambient_mem E hn; rewrite (ambient_normalizer injE) in h.
  exact: (setIP h).2.
have hJ : E n \in normalizer_intersection by apply/setIP; split.
have ha : conj_aut P n \in normalizer_action_image.
  rewrite -(normalizer_action_subgroup injE hn).
  exact (mem_morphim (normalizer_morphism injE P) hEn hJ).
have hi := subsetP (normalizer_action_image_inner hr) _ ha.
have /morphimP[q _ hq ea] := hi.
have hC : n*q^-1 \in 'C(P).
  apply/centP=> x hx; apply/esym/commgP/conjg_fixP.
  rewrite conjgM -(@norm_conj_autE N P n x hn hx) ea conj_autE // conjgK.
  by [].
have hh := groupM (subsetP (DPFusionCentricCriterion.centric_self_centralizing hc) _ hC) hq.
by rewrite mulgKV in hh.
Qed.

Theorem normal_p_subgroup_contained :
  DPFusionSystem.centric F P -> DPFusionRadical.radical F p P -> O \subset AP.
Proof.
move=> hc hr.
have hs : from_ambient E O \subset P :=
  normal_subgroup_contained_of_normalizer_inter pN source_preimage_normal
    (normalizer_intersection_contained hc hr).
have him := morphimS E hs.
have ho := ambient_from sOT.
change (is_true (ambient E (from_ambient E O) \subset AP)) in him.
by rewrite ho in him.
Qed.
End Radical.
End DPFiniteGroupFusionEmbeddingRadical.
