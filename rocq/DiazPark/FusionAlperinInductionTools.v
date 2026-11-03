From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy FusionSaturationImage
  FusionAlperinWords FusionAlperinWordOperations.
Import DPFusion DPFusionAlperinWords.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAlperinInductionTools.
Section Tools.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma subgroup_card_top (P : {group S}) : #|P| = #|S| -> P = [set: S]%G.
Proof.
move=> hc; apply: val_inj; apply/eqP.
by rewrite eqEcard subsetT /= cardsT hc.
Qed.

Lemma centric_top : DPFusionSystem.centric F [set: S]%G.
Proof.
apply/forallP=> Q; apply/implyP=> hQ.
have hc := DPFusionConjugacy.conjugate_card hQ.
have -> : Q = [set: S]%G by apply: subgroup_card_top; rewrite -hc cardsT.
exact: subsetT.
Qed.

Lemma extension_target_in_image (P Q A B : {group S}) (f : DPFusion.map P Q)
    (h : DPFusion.map A B) :
  P \subset A -> DPFusion.image f = Q -> {in P, h =1 f} ->
  Q \subset DPFusion.image h.
Proof.
move=> sPA onto hext; apply/subsetP=> y Qy.
have /morphimP[x Px _ ey] : y \in DPFusion.image f by rewrite onto.
apply/morphimP; exists x; try exact: subsetP sPA x Px.
rewrite DPFusion.map_morphismE (hext x Px).
exact ey.
Qed.

Lemma strongly_factorizable_of_extension (P Q A B : {group S}) (f : DPFusion.map P Q)
    (h : DPFusion.map A B) :
  P \subset A -> DPFusion.image f = Q -> {in P, h =1 f} ->
  strongly_factorizable F (DPFusion.to_image h) -> strongly_factorizable F f.
Proof.
move=> sPA onto hext hgen.
apply: (strongly_factorizable_restrict hgen sPA (extension_target_in_image sPA onto hext)).
move=> x Px; rewrite DPFusion.to_image_in ?(subsetP sPA) //; symmetry.
exact: hext x Px.
Qed.

End Tools.
End DPFusionAlperinInductionTools.

