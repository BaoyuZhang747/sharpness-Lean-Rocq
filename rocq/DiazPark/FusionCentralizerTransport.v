From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms
  GroupKNormalizer FusionCentralizerMaps FusionCentralizer FusionCentralizerAut
  FusionCentralizerCompression.
Import DPFusion DPFusionSubgroup DPFusionCentralizer DPFusionAutomorphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerTransport.
Section Transport.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.
Variables (P : {group T}) (B : {group S}).
Variable theta : DPFusion.map (joint P) B.
Hypothesis onto : DPFusion.image theta = B.
Local Notation KP := (DPFusionCentralizerAut.K F E P).
Local Notation KT := (aut_transport_group theta KP).
Definition transported_normalizer := k_normalizer [set: S]%G B KT.
Definition imageP : {group S} := (DPFusion.map_morphism theta @* ambient P)%G.
Local Notation E' := (DPFusionCentralizerCompression.imageE theta).

Lemma transported_K_fixes a : a \in KT -> {in E', a =1 id}.
Proof.
move=> /morphimP[b _ Kb ->] y.
rewrite DPFusionCentralizerCompression.imageE_eq=> /morphimP[e _ Ee ->].
have be : b \in Aut (joint P).
  exact: (subsetP (DPFusionSaturation.aut_group_sub F (joint P)) _
    (subsetP (DPFusionCentralizerAut.K_sub F E P) _ Kb)).
change (aut_transport theta b (theta e) = theta e).
rewrite aut_transportE // ?(subsetP (joint_right P) e Ee) //.
by rewrite (DPFusionCentralizerAut.K_fixes Kb Ee).
Qed.

Lemma transported_K_preserves a : a \in KT -> {in imageP, forall x, a x \in imageP}.
Proof.
move=> /morphimP[b _ Kb ->] y /morphimP[x _ Px ->].
have bx : b \in Aut (joint P).
  exact: (subsetP (DPFusionSaturation.aut_group_sub F (joint P)) _
    (subsetP (DPFusionCentralizerAut.K_sub F E P) _ Kb)).
change (aut_transport theta b (theta x) \in imageP).
rewrite aut_transportE // ?(subsetP (joint_left P) x Px) //.
apply: mem_morphim; first exact: (subsetP (joint_left P) _ (DPFusionCentralizerAut.K_preserves Kb Px)).
exact: (DPFusionCentralizerAut.K_preserves Kb Px).
Qed.

Lemma transported_normalizer_centralizes : transported_normalizer \subset 'C(E').
Proof.
apply/subsetP=> s /morphpreP[/setIP[_ Ns] Ks].
change (is_true (conj_aut B s \in KT)) in Ks.
apply/centP=> e Ee; apply/esym/commgP/conjg_fixP.
have eB : e \in B.
  rewrite DPFusionCentralizerCompression.imageE_eq in Ee.
  have /morphimP[x _ Ex ->] := Ee.
  exact: (DPFusion.map_into theta (subsetP (joint_right P) x Ex)).
rewrite -(norm_conj_autE Ns eB).
exact: (transported_K_fixes Ks Ee).
Qed.

Lemma transported_normalizer_normalizes : transported_normalizer \subset 'N(imageP).
Proof.
apply/subsetP=> s /morphpreP[/setIP[_ Ns] Ks].
change (is_true (conj_aut B s \in KT)) in Ks.
rewrite inE; apply/subsetP=> y /imsetP[x Px ->].
have xB : x \in B.
  have /morphimP[z _ Pz ->] := Px.
  exact: (DPFusion.map_into theta (subsetP (joint_left P) z Pz)).
rewrite -(norm_conj_autE Ns xB).
exact: (transported_K_preserves Ks Px).
Qed.

End Transport.
End DPFusionCentralizerTransport.


