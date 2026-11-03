From mathcomp Require Import all_ssreflect all_fingroup pgroup nilpotent sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionOrbit
  FusionCentricBasics FusionCentricHomRestriction FusionOuterAutomorphisms FusionOuterCard.
Import DPFusion DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentricHomCount.
Section Count.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable T : {group S}.

Theorem hom_card_end_mod (P : {group S}) :
  P \subset T -> DPFusionSystem.centric F P ->
  (#|[set: orbit_hom F P T]| %% p = #|[set: orbit_hom F T T]| %% p)%N.
Proof.
have main : forall n (P : {group S}), (#|T| - #|P|)%N = n ->
    P \subset T -> DPFusionSystem.centric F P ->
    (#|[set: orbit_hom F P T]| %% p = #|[set: orbit_hom F T T]| %% p)%N.
  move=> n; elim/ltn_ind: n=> n ih P0 hn sPT hc.
  case: (boolP (P0 == T))=> [/eqP -> //|neP].
  have prPT : P0 \proper T by rewrite properEneq neP sPT.
  have pT : p.-group T := pgroupS (subsetT _) pS.
  have growth := nilpotent_proper_norm (pgroup_nil pT) prPT.
  pose N := 'N_T(P0)%G.
  have sPN : P0 \subset N := proper_sub growth.
  have sNT : N \subset T := subsetIl _ _.
  have sNN : N \subset 'N(P0) := subsetIr _ _.
  have hcN := DPFusionCentricBasics.centric_overgroup sPN hc.
  have growcard : (#|P0| < #|N|)%N := proper_card growth.
  have measure : (#|T| - #|N| < n)%N.
    by rewrite -hn ltn_sub2lE ?(subset_leq_card sNT).
  rewrite (@DPFusionCentricHomRestriction.hom_card_mod S F p pS sat P0 N T sPN sNN hc).
  exact: (ih _ measure N erefl sNT hcN).
exact: main _ P erefl.
Qed.

Theorem hom_card_outer_mod (P : {group S}) :
  P \subset T -> DPFusionSystem.centric F P ->
  (#|[set: orbit_hom F P T]| %% p = #|DPFusionOuter.outer_group F T| %% p)%N.
Proof.
move=> sPT hc; rewrite hom_card_end_mod // DPFusionOuterCard.endomorphism_card_outer.
by [].
Qed.

End Count.

Theorem top_hom_coprime (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (hp : prime p) (pS : p.-group [set: S])
    (sat : DPFusionSaturation.saturated F p) (P : {group S}) :
  DPFusionSystem.centric F P -> coprime p #|[set: orbit_hom F P [set: S]%G]|.
Proof.
move=> hc; rewrite -coprime_modr (hom_card_end_mod pS sat (subsetT P) hc) coprime_modr.
exact: DPFusionOuterCard.top_endomorphism_coprime hp sat.
Qed.
End DPFusionCentricHomCount.



