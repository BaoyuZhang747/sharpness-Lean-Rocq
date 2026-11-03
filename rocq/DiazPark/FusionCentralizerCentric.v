From mathcomp Require Import all_ssreflect all_fingroup center pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionConjugacy
  FusionCentricCriterion FusionCentricBasics FusionCentralizerMaps FusionCentralizer
  FusionCentralizerCentral FusionCentralizerAmbient FusionCentralizerSaturation.
Import DPFusion DPFusionSubgroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerCentric.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.
Local Notation CF := (DPFusionCentralizer.system F E).

Lemma ambient_centralizer (P : {group T}) :
  (ambient 'C(P)%G : {set S}) = C :&: 'C(ambient P).
Proof.
change (sgval @* 'C(P) = C :&: 'C(sgval @* P)).
by rewrite (injm_cent (injm_sgval _) (subsetT P)) im_sgval.
Qed.

Lemma conjugate_ambient (P Q : {group T}) :
  DPFusionSystem.conjugate CF P Q ->
  DPFusionSystem.conjugate F (ambient P) (ambient Q).
Proof.
move=> /existsP[f /andP[hf /eqP onto]].
apply/existsP; exists (DPFusionSubgroup.lift f); apply/andP; split.
- exact: DPFusionCentralizerAmbient.lift_allowed hf.
- by rewrite lift_image onto.
Qed.

Theorem ambient_centric_centralizer_centric (P : {group T}) :
  DPFusionSystem.centric F (ambient P) -> DPFusionSystem.centric CF P.
Proof.
move=> hP; apply/forallP=> Q; apply/implyP=> hPQ.
have hc : 'C(ambient Q) \subset ambient Q :=
  implyP (forallP hP (ambient Q)) (conjugate_ambient hPQ).
apply/subsetP=> x Cx.
have hx : val x \in ambient 'C(Q)%G := ambient_mem Cx.
rewrite ambient_centralizer in hx.
have h := ambient_repr (subsetP hc _ (setIP hx).2).
by rewrite sgvalK in h.
Qed.

Hypothesis abE : abelian E.

Lemma embedded_sub_of_centric (P : {group T}) :
  DPFusionSystem.centric CF P -> DPFusionCentralizerCentral.embedded E \subset P.
Proof.
move=> hP.
have hE := DPFusionCentralizerCentral.embedded_sub_center abE.
have hC : DPFusionCentralizerCentral.embedded E \subset 'C(P).
  have h0 : DPFusionCentralizerCentral.embedded E \subset 'C([set: T]) :=
    subset_trans hE (subsetIr [set: T] 'C([set: T])).
  exact: (subset_trans h0 (centS (subsetT P))).
exact: subset_trans hC (DPFusionCentricCriterion.centric_self_centralizing hP).
Qed.

Lemma E_sub_of_centric (P : {group T}) :
  DPFusionSystem.centric CF P -> E \subset ambient P.
Proof.
move=> hP.
have h := morphimS (@sgval S C) (embedded_sub_of_centric hP).
change (is_true (ambient (DPFusionCentralizerCentral.embedded E) \subset ambient P)) in h.
by rewrite DPFusionCentralizerCentral.embedded_ambient // in h.
Qed.

Lemma joint_eq_of_centric (P : {group T}) :
  DPFusionSystem.centric CF P -> DPFusionCentralizer.joint P = ambient P.
Proof.
move=> hP; apply: val_inj.
change (ambient P <*> E = ambient P).
apply/joing_idPl; exact: E_sub_of_centric hP.
Qed.

Lemma ambient_self_centralizing_of_centric (P : {group T}) :
  DPFusionSystem.centric CF P -> 'C(ambient P) \subset ambient P.
Proof.
move=> hP.
have h := morphimS (@sgval S C) (DPFusionCentricCriterion.centric_self_centralizing hP).
change (is_true (ambient 'C(P)%G \subset ambient P)) in h.
rewrite ambient_centralizer in h.
have hc : 'C(ambient P) \subset C := centS (E_sub_of_centric hP).
have he : C :&: 'C(ambient P) = 'C(ambient P) by apply/setIidPr.
by rewrite he in h.
Qed.

Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Hypothesis hE : DPFusionSystem.fully_centralized F E.

Theorem centralizer_centric_ambient_centric (P : {group T}) :
  DPFusionSystem.centric CF P -> DPFusionSystem.centric F (ambient P).
Proof.
move=> hP.
have [Q [hPQ hQ]] := DPFusionConjugacy.fully_normalized_conjugate_exists CF P.
have cQ := DPFusionCentricBasics.centric_conjugate hPQ hP.
have fcQ := DPFusionCentralizerSaturation.fully_normalized_joint_centralized abE pS sat hE hQ.
rewrite (joint_eq_of_centric cQ) in fcQ.
have aQ : DPFusionSystem.centric F (ambient Q).
  apply/(DPFusionCentricCriterion.saturated_centric_iff sat); split=> //.
  exact: ambient_self_centralizing_of_centric cQ.
apply: DPFusionCentricBasics.centric_conjugate _ aQ.
exact: DPFusionConjugacy.conjugate_reverse (conjugate_ambient hPQ).
Qed.

Theorem centralizer_centric_iff (P : {group T}) :
  (DPFusionSystem.centric CF P <-> DPFusionSystem.centric F (ambient P)) /\
  (DPFusionSystem.centric CF P -> E \subset ambient P).
Proof.
split; last exact: E_sub_of_centric.
split; [exact: centralizer_centric_ambient_centric | exact: ambient_centric_centralizer_centric].
Qed.
End Comparison.
End DPFusionCentralizerCentric.

