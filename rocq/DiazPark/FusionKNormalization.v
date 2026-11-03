From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy
  FusionAutomorphisms FusionSylowAdjustment GroupKNormalizer.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionKNormalization.
Import DPFusionAutomorphisms DPFusionSylowAdjustment.

Section KGroups.
Variable S : finGroupType.

Lemma ambient_automorphism_group_full (P : {group S}) :
  ambient_automorphism_group [set: S]%G P = DPFusionSaturation.ambient_aut_group P.
Proof.
apply: val_inj; change ((restrm (subsetIr [set: S] 'N(P)) (conj_aut P) @*
  'N_[set: S](P)) = conj_aut P @* 'N(P)).
by rewrite morphim_restrm setTI setIid.
Qed.

Lemma k_normalizer_card_full (P : {group S}) (K : {group {perm S}}) :
  #|k_normalizer [set: S]%G P K| =
  (#|'C(P)| * #|DPFusionSaturation.ambient_aut_group P :&: K|)%N.
Proof.
rewrite k_normalizer_card.
change (#|'C_[set: S](P)| *
  #|ambient_automorphism_group [set: S]%G P :&: K| =
  #|'C(P)| * #|DPFusionSaturation.ambient_aut_group P :&: K|)%N.
by rewrite setTI ambient_automorphism_group_full.
Qed.

Lemma k_automizer_pgroup (p : nat) (P : {group S}) (K : {group {perm S}}) :
  p.-group [set: S] -> p.-group (DPFusionSaturation.ambient_aut_group P :&: K).
Proof.
move=> hS.
exact: (pgroupS (subsetIl (DPFusionSaturation.ambient_aut_group P) K)
  (ambient_aut_pgroup P hS)).
Qed.

Lemma card_pgroup_le_sylow (p : nat) (G H T : {group S}) :
  p.-Sylow(G) T -> H \subset G -> p.-group H -> (#|H| <= #|T|)%N.
Proof.
move=> sylT sHG pH; have [x Gx hsub] := Sylow_Jsub sylT sHG pH.
have hcard := subset_leq_card hsub.
by rewrite cardJg in hcard.
Qed.

End KGroups.

Section FusionKGroups.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition fully_K_normalized (P : {group S}) (K : {group {perm S}}) : Prop :=
  forall (Q : {group S}) (f : DPFusion.map P Q),
    DPFusionSystem.allowed F f -> DPFusion.image f = Q ->
    (#|k_normalizer [set: S]%G Q (aut_transport_group f K)| <=
      #|k_normalizer [set: S]%G P K|)%N.

Theorem exists_fully_centralized_K_sylow (p : nat)
    (hS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (P : {group S}) (K : {group {perm S}}) :
  K \subset DPFusionSaturation.aut_group F P ->
  exists (Q : {group S}) (f : DPFusion.map P Q),
    DPFusionSystem.allowed F f /\ DPFusion.image f = Q /\
    DPFusionSystem.fully_centralized F Q /\
    p.-Sylow(aut_transport_group f K)
      (DPFusionSaturation.ambient_aut_group Q :&: aut_transport_group f K).
Proof.
move=> sKF.
have [Q [hPQ hQ]] := DPFusionConjugacy.fully_normalized_conjugate_exists F P.
have /existsP[f /andP[hf /eqP onto]] := hPQ.
have [hCQ sylQ] := DPFusionSaturation.saturation_fully_normalized sat hQ.
have [H sylH] := Sylow_exists p K.
have sHF := subset_trans (pHall_sub sylH) sKF.
have [g [hg [ontog hT]]] := sylow_adjust_transport hf onto sHF
  (pHall_pgroup sylH) sylQ.
exists Q, g; split=> //; split=> //; split=> //.
have sKA := subset_trans sKF (DPFusionSaturation.aut_group_sub F P).
have sHA := subset_trans (pHall_sub sylH) sKA.
have sylT : p.-Sylow(aut_transport_group g K) (aut_transport_group g H).
  exact: morphim_pHall sHA sylH.
have sTK : aut_transport_group g H \subset aut_transport_group g K.
  exact: morphimS _ (pHall_sub sylH).
have sTD : aut_transport_group g H \subset
    DPFusionSaturation.ambient_aut_group Q :&: aut_transport_group g K.
  by apply/subsetIP; split.
have pD := k_automizer_pgroup Q (aut_transport_group g K) hS.
have eqD := sub_pHall sylT pD sTD (subsetIr _ _).
by rewrite eqD.
Qed.

Theorem fully_K_normalized_properties (p : nat)
    (hS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (P : {group S}) (K : {group {perm S}}) :
  K \subset DPFusionSaturation.aut_group F P -> fully_K_normalized P K ->
  DPFusionSystem.fully_centralized F P /\
    p.-Sylow(K) (DPFusionSaturation.ambient_aut_group P :&: K).
Proof.
move=> sKF hPK.
have [Q [f [hf [onto [hCQ sylQ]]]]] := exists_fully_centralized_K_sylow hS sat sKF.
pose KQ := aut_transport_group f K.
pose DP := (DPFusionSaturation.ambient_aut_group P :&: K)%G.
pose DQ := (DPFusionSaturation.ambient_aut_group Q :&: KQ)%G.
have sKA := subset_trans sKF (DPFusionSaturation.aut_group_sub F P).
have sDPK : DP \subset K := subsetIr _ _.
have sDPA := subset_trans sDPK sKA.
have pDP : p.-group DP := k_automizer_pgroup P K hS.
have pTD : p.-group (aut_transport_group f DP) := morphim_pgroup _ pDP.
have sTDK : aut_transport_group f DP \subset KQ := morphimS _ sDPK.
have hD : (#|DP| <= #|DQ|)%N.
  have h := card_pgroup_le_sylow sylQ sTDK pTD.
  by rewrite (aut_transport_group_card f sDPA) in h.
have hPQ : DPFusionSystem.conjugate F P Q.
  by apply/existsP; exists f; rewrite hf onto eqxx.
have hQP := DPFusionConjugacy.conjugate_reverse hPQ.
have hC : (#|'C(P)| <= #|'C(Q)|)%N := implyP (forallP hCQ P) hQP.
have hmul := hPK Q f hf onto.
rewrite !k_normalizer_card_full in hmul.
change (is_true (#|'C(Q)| * #|DQ| <= #|'C(P)| * #|DP|)%N) in hmul.
have hCback : (#|'C(Q)| <= #|'C(P)|)%N.
  rewrite -(leq_pmul2r (cardG_gt0 DP)).
  exact: leq_trans (leq_mul (leqnn _) hD) hmul.
have hCeq : #|'C(P)| = #|'C(Q)|.
  by apply/eqP; rewrite eqn_leq; apply/andP; split.
have hDback : (#|DQ| <= #|DP|)%N.
  rewrite -(leq_pmul2l (cardG_gt0 'C(P)%G)).
  exact: leq_trans (leq_mul hC (leqnn _)) hmul.
have hDeq : #|DP| = #|DQ|.
  by apply/eqP; rewrite eqn_leq; apply/andP; split.
have hKcard : #|KQ| = #|K| := aut_transport_group_card f sKA.
split.
- apply/forallP=> R; apply/implyP=> hPR; rewrite hCeq.
  apply: (implyP (forallP hCQ R)).
  exact: DPFusionConjugacy.conjugate_trans hQP hPR.
- apply/pHallP; split; first exact: sDPK.
  change (#|DP| = (#|K|`_p)%N).
  by rewrite hDeq (card_Hall sylQ) hKcard.
Qed.

End FusionKGroups.
End DPFusionKNormalization.
