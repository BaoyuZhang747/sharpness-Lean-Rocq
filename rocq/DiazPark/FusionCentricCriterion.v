From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionConjugacy FusionReceptivity.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentricCriterion.
Section Centric.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma centric_self_centralizing (P : {group S}) :
  DPFusionSystem.centric F P -> 'C(P) \subset P.
Proof.
move=> hP; exact: (implyP (forallP hP P) (DPFusionConjugacy.conjugate_refl F P)).
Qed.

Lemma centric_fully_centralized (P : {group S}) :
  DPFusionSystem.centric F P -> DPFusionSystem.fully_centralized F P.
Proof.
move=> hP; apply/forallP=> Q; apply/implyP=> hPQ.
have sCQ : 'C(Q) \subset Q := implyP (forallP hP Q) hPQ.
have /existsP[f /andP[hf /eqP onto]] := DPFusionConjugacy.conjugate_reverse hPQ.
have hc : DPFusion.map_morphism f @* 'C(Q) \subset 'C(P).
  have hi : DPFusion.map_morphism f @* Q = P.
    change (val (DPFusion.image f) = val P); by rewrite onto.
  rewrite -hi; exact: morphim_cent.
have hcard := subset_leq_card hc.
by rewrite (card_injm (DPFusion.map_injm f) sCQ) in hcard.
Qed.

Theorem receptive_self_centralizing_centric (P : {group S}) :
  DPFusionReceptivity.receptive F P -> 'C(P) \subset P -> DPFusionSystem.centric F P.
Proof.
move=> hrec sCP; apply/forallP=> Q; apply/implyP=> hPQ.
have /existsP[f /andP[hf /eqP onto]] := DPFusionConjugacy.conjugate_reverse hPQ.
have [fhat [hhat hext]] := hrec Q f hf onto.
have hC := @DPFusionReceptivity.extension_centralizer_image S Q P f onto fhat hext.
apply/subsetP=> s Cs.
have Ns : s \in DPFusionSaturation.extension_domain f :=
  subsetP (DPFusionSaturation.centralizer_extension_domain f) s Cs.
have Is : fhat s \in DPFusion.map_morphism fhat @* 'C(Q).
  by apply/morphimP; exists s.
have Ps : fhat s \in P := subsetP sCP _ (subsetP hC _ Is).
have Ips : fhat s \in DPFusion.image f by rewrite onto.
have /morphimP[q Qq _ hq] := Ips.
change (fhat s = DPFusion.map_fun f q) in hq.
have Nq : q \in DPFusionSaturation.extension_domain f :=
  subsetP (DPFusionSaturation.source_extension_domain f) q Qq.
have hs : s = q.
  apply: (DPFusion.map_injective (f := fhat) Ns Nq).
  exact: eq_trans hq (esym (hext q Qq)).
by rewrite hs.
Qed.

Theorem saturated_centric_iff (p : nat) (sat : DPFusionSaturation.saturated F p)
    (P : {group S}) :
  DPFusionSystem.centric F P <->
    DPFusionSystem.fully_centralized F P /\ 'C(P) \subset P.
Proof.
split.
- move=> hP; split; [exact: centric_fully_centralized hP | exact: centric_self_centralizing hP].
- move=> [hP hC]; apply: receptive_self_centralizing_centric _ hC.
  exact (@DPFusionReceptivity.saturated_receptive S F p sat P hP).
Qed.

End Centric.
End DPFusionCentricCriterion.



