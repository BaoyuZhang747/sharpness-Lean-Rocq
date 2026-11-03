From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms
  FusionKNormalization FusionReceptivity FusionReceptivityCriterion FusionQuotientMaps
  GroupKNormalizer FusionCentralizerMaps FusionCentralizer FusionCentralizerAut
  FusionCentralizerAutNormalizer FusionCentralizerReceptive
  FusionCentralizerTransport FusionCentralizerNormalized FusionCentralizerCentral.
Import DPFusion DPFusionSubgroup DPFusionCentralizer DPFusionAutomorphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerSaturation.
Section Saturation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Hypothesis abE : abelian E.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Hypothesis hE : DPFusionSystem.fully_centralized F E.
Local Notation T := [subg 'C(E)%G]%type.
Local Notation CF := (system F E).

Lemma centralizer_pgroup : p.-group [set: T].
Proof.
have pC : p.-group 'C(E) := pgroupS (subsetT _) pS.
have h := morphim_pgroup (subg 'C(E)%G) pC.
by rewrite im_subg in h.
Qed.

Lemma fully_normalized_K (P : {group T}) :
  DPFusionSystem.fully_normalized CF P ->
  DPFusionKNormalization.fully_K_normalized F (joint P) (DPFusionCentralizerAut.K F E P).
Proof.
move=> hP B theta htheta onto.
rewrite DPFusionCentralizerAutNormalizer.k_normalizerE.
change (is_true (#|DPFusionCentralizerTransport.transported_normalizer F theta| <=
  #|sgval @* 'N(P)|)%N).
rewrite (card_injm (injm_sgval _) (subsetT _)).
exact: (DPFusionCentralizerNormalized.fully_normalized_transport_card abE sat hE hP htheta onto).
Qed.

Lemma fully_normalized_joint_centralized (P : {group T}) :
  DPFusionSystem.fully_normalized CF P -> DPFusionSystem.fully_centralized F (joint P).
Proof.
move=> hP.
exact: (proj1 (DPFusionKNormalization.fully_K_normalized_properties pS sat
  (DPFusionCentralizerAut.K_sub F E P) (fully_normalized_K hP))).
Qed.

Lemma fully_normalized_receptive (P : {group T}) :
  DPFusionSystem.fully_normalized CF P -> DPFusionReceptivity.receptive CF P.
Proof.
move=> hP; exact: (DPFusionCentralizerReceptive.receptive_of_joint_fully_centralized
  abE sat (fully_normalized_joint_centralized hP)).
Qed.

Lemma fully_normalized_sylow (P : {group T}) :
  DPFusionSystem.fully_normalized CF P ->
  p.-Sylow(DPFusionSaturation.aut_group CF P) (DPFusionSaturation.ambient_aut_group P).
Proof.
move=> hP; apply: DPFusionCentralizerAutNormalizer.restriction_sylow.
exact: (proj2 (DPFusionKNormalization.fully_K_normalized_properties pS sat
  (DPFusionCentralizerAut.K_sub F E P) (fully_normalized_K hP))).
Qed.

(** The actual centralizer system of any abelian fully F-centralized E is
    saturated. In particular no nontriviality or exponent-p assumption occurs. *)
Theorem centralizer_saturated : DPFusionSaturation.saturated CF p.
Proof.
apply: (@DPFusionReceptivityCriterion.saturated_of_normalized_receptive_sylow
  [the finGroupType of T] CF p centralizer_pgroup).
move=> P hP; split.
- exact: fully_normalized_receptive hP.
- exact: fully_normalized_sylow hP.
Qed.

Theorem centralizer_saturated_central :
  DPFusionSaturation.saturated CF p /\
  DPFusionQuotient.central CF (DPFusionCentralizerCentral.embedded E).
Proof.
split; first exact: centralizer_saturated.
exact: (DPFusionCentralizerCentral.embedded_central F abE).
Qed.
End Saturation.
End DPFusionCentralizerSaturation.




