From mathcomp Require Import all_ssreflect all_fingroup center.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturationImage
  FusionConjugacy FusionCentricCriterion.
Import DPFusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentricBasics.
Section Centric.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma centric_conjugate (P Q : {group S}) :
  DPFusionSystem.conjugate F P Q ->
  DPFusionSystem.centric F P -> DPFusionSystem.centric F Q.
Proof.
move=> hPQ hP; apply/forallP=> R; apply/implyP=> hQR.
exact: implyP (forallP hP R) (DPFusionConjugacy.conjugate_trans hPQ hQR).
Qed.

Lemma centric_image (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> DPFusionSystem.centric F P ->
  DPFusionSystem.centric F (DPFusion.image f).
Proof.
move=> hf hP; apply: centric_conjugate _ hP.
apply/existsP; exists (DPFusion.to_image f); apply/andP; split.
- exact: DPFusionSystem.image_closed hf.
- by rewrite DPFusionSaturationImage.image_to_image.
Qed.

Lemma centric_overgroup (P Q : {group S}) :
  P \subset Q -> DPFusionSystem.centric F P -> DPFusionSystem.centric F Q.
Proof.
move=> sPQ hP; apply/forallP=> R; apply/implyP.
move=> /existsP[f /andP[hf /eqP onto]].
pose g := DPFusion.restrict f sPQ.
have hg : DPFusionSystem.allowed F g := DPFusionSystem.restriction_allowed sPQ hf.
have hc := DPFusionCentricCriterion.centric_self_centralizing (centric_image hg hP).
have sIR : DPFusion.image g \subset R := DPFusion.image_sub g.
exact: subset_trans (centS sIR) (subset_trans hc sIR).
Qed.

Lemma centric_centralizer_center (P : {group S}) :
  DPFusionSystem.centric F P -> 'C(P) = 'Z(P).
Proof.
move=> hP; rewrite /center.
apply/esym/setIidPr; exact: DPFusionCentricCriterion.centric_self_centralizing hP.
Qed.

End Centric.
End DPFusionCentricBasics.
