From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** Receptivity has its ordinary extension meaning. The centralizer injection
    below is constructed from an actual extension, not assumed as a field. *)
Module DPFusionReceptivity.

Section ExtensionCentralizers.
Variable S : finGroupType.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Hypothesis onto : DPFusion.image f = Q.
Variable fhat : DPFusion.map (DPFusionSaturation.extension_domain f) [set: S]%G.
Hypothesis extends : {in P, fhat =1 f}.

Lemma extension_source_image : DPFusion.map_morphism fhat @* P = Q.
Proof.
have heq : DPFusion.map_morphism fhat @* P = DPFusion.map_morphism f @* P.
  rewrite !morphimEsub ?DPFusionSaturation.source_extension_domain //.
  apply: eq_in_imset=> x Px; exact: extends Px.
change (DPFusion.map_morphism fhat @* P = val Q).
rewrite heq; change (val (DPFusion.image f) = val Q).
by rewrite onto.
Qed.

Lemma extension_centralizer_image :
  DPFusion.map_morphism fhat @* 'C(P) \subset 'C(Q).
Proof.
rewrite -extension_source_image.
exact: morphim_cent.
Qed.

Lemma extension_centralizer_card : (#|'C(P)| <= #|'C(Q)|)%N.
Proof.
have h := subset_leq_card extension_centralizer_image.
rewrite (card_injm (DPFusion.map_injm fhat)
  (DPFusionSaturation.centralizer_extension_domain f)) in h.
exact: h.
Qed.

Lemma restricted_centralizer_image :
  DPFusion.image (DPFusion.restrict fhat (DPFusionSaturation.centralizer_extension_domain f))
    \subset 'C(Q).
Proof.
change (DPFusion.map_morphism
  (DPFusion.restrict fhat (DPFusionSaturation.centralizer_extension_domain f)) @*
  'C(P) \subset 'C(Q)).
rewrite /DPFusion.restrict /DPFusion.of_morphism DPFusion.of_morphism_image im_restrm.
exact: extension_centralizer_image.
Qed.

Definition centralizer_extension : DPFusion.map 'C(P)%G 'C(Q)%G :=
  DPFusion.corestrict restricted_centralizer_image.

Lemma centralizer_extensionE : {in 'C(P), centralizer_extension =1 fhat}.
Proof.
move=> x Cx; rewrite /centralizer_extension DPFusion.corestrict_in //.
exact: DPFusion.restrict_in.
Qed.

End ExtensionCentralizers.

Section Receptivity.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition receptive (Q : {group S}) : Prop :=
  forall (P : {group S}) (f : DPFusion.map P Q),
    DPFusionSystem.allowed F f -> DPFusion.image f = Q ->
    exists fhat : DPFusion.map (DPFusionSaturation.extension_domain f) [set: S]%G,
      DPFusionSystem.allowed F fhat /\ {in P, fhat =1 f}.

Theorem receptive_fully_centralized (Q : {group S}) :
  receptive Q -> DPFusionSystem.fully_centralized F Q.
Proof.
move=> hrec; apply/forallP=> P; apply/implyP=> hQP.
have /existsP[f /andP[hf /eqP onto]] := DPFusionConjugacy.conjugate_reverse hQP.
have [fhat [_ hext]] := hrec P f hf onto.
exact (@extension_centralizer_card S P Q f onto fhat hext).
Qed.

Lemma saturated_receptive p (sat : DPFusionSaturation.saturated F p)
    (Q : {group S}) : DPFusionSystem.fully_centralized F Q -> receptive Q.
Proof.
move=> hQ P f hf onto.
exact (@DPFusionSaturation.saturation_extension S F p sat P Q f hf onto hQ).
Qed.

Lemma saturated_fully_normalized_receptive p
    (sat : DPFusionSaturation.saturated F p) (Q : {group S}) :
  DPFusionSystem.fully_normalized F Q ->
  receptive Q /\ p.-Sylow(DPFusionSaturation.aut_group F Q)
    (DPFusionSaturation.ambient_aut_group Q).
Proof.
move=> hQ; have [hC hSyl] := DPFusionSaturation.saturation_fully_normalized sat hQ.
split=> //; exact (@saturated_receptive p sat Q hC).
Qed.

End Receptivity.
End DPFusionReceptivity.
