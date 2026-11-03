From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionReceptivity.
From DiazPark Require Import FusionCentralizerMaps FusionCentralizer FusionCentralizerExtension.
Import DPFusion DPFusionSubgroup DPFusionCentralizer DPFusionCentralizerExtension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerReceptive.
Section Receptive.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Hypothesis abE : abelian E.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.

Lemma ambient_top : ambient [set: T]%G = C.
Proof. apply: val_inj; exact: im_sgval. Qed.

Lemma joint_sub (P : {group T}) : joint P \subset C.
Proof. by rewrite /joint join_subG ambient_sub; exact: abE. Qed.

Lemma joint_top : joint [set: T]%G = C.
Proof.
apply: val_inj; change (ambient [set: T]%G <*> E = C).
rewrite ambient_top; by apply/joing_idPl.
Qed.

Lemma fixing_extension_image (P : {group T})
    (g : DPFusion.map (joint P) [set: S]%G) (gfix : {in E, g =1 id}) :
  DPFusion.image g \subset C.
Proof.
have imE : DPFusion.map_morphism g @* E = E.
  apply/setP=> e; apply/idP/idP.
  - by case/morphimP=> x _ Ex ->; rewrite DPFusion.map_morphismE gfix.
  - move=> Ee; apply/morphimP; exists e=> //.
    + exact: subsetP (joint_right P) e Ee.
    + by rewrite DPFusion.map_morphismE gfix.
have h := morphim_cents (DPFusion.map_morphism g) (joint_sub P).
by rewrite imE in h.
Qed.

Theorem receptive_of_joint_fully_centralized p (sat : DPFusionSaturation.saturated F p)
    (Q : {group T}) (hQ : DPFusionSystem.fully_centralized F (joint Q)) :
  DPFusionReceptivity.receptive (system F E) Q.
Proof.
move=> P f /allowedP[fhat [hf [hext hfix]]] onto.
have ontohat : DPFusion.image fhat = joint Q by rewrite (extension_image hext hfix) onto.
have [ghat [hg gext]] := DPFusionSaturation.saturation_extension sat hf ontohat hQ.
have sD := extension_domain_joint hext hfix.
pose D := DPFusionSaturation.extension_domain f.
pose g1 := DPFusion.restrict ghat sD.
have hg1 : DPFusionSystem.allowed F g1 := DPFusionSystem.restriction_allowed sD hg.
have gfix : {in E, g1 =1 id}.
  move=> e Ee; rewrite /g1 DPFusion.restrict_in ?(subsetP (joint_right D) e Ee) //.
  by rewrite gext ?(subsetP (joint_right P) e Ee) // hfix.
have range1 : DPFusion.image g1 \subset C := fixing_extension_image gfix.
pose g2 := DPFusion.corestrict range1.
have hg2 : DPFusionSystem.allowed F g2 := DPFusionSystem.corestriction_allowed range1 hg1.
pose g3 := reindex (erefl (joint D)) (esym ambient_top) g2.
pose g0 := DPFusion.restrict g3 (joint_left D).
pose g := lower g0.
have hallow : DPFusionSystem.allowed (system F E) g.
  apply/allowedP; exists (reindex (erefl (joint D)) (esym joint_top) g2); split.
  - exact: reindex_allowed hg2.
  - split.
    + move=> x Dx; rewrite reindexE /g lowerE // /g0 DPFusion.restrict_in ?ambient_mem //.
      by rewrite /g3 reindexE.
    + move=> e Ee; rewrite reindexE /g2 DPFusion.corestrict_in ?(subsetP (joint_right D) e Ee) //.
      exact: gfix Ee.
exists g; split=> //; move=> x Px; apply: val_inj.
have xD : x \in D := subsetP (DPFusionSaturation.source_extension_domain f) x Px.
have vxP : val x \in joint P := subsetP (joint_left P) _ (ambient_mem Px).
have vxD : val x \in joint D := subsetP (joint_left D) _ (ambient_mem xD).
rewrite /g lowerE // /g0 DPFusion.restrict_in ?ambient_mem // /g3 reindexE.
rewrite /g2 DPFusion.corestrict_in // /g1 DPFusion.restrict_in //.
by rewrite gext // hext.
Qed.
End Receptive.
End DPFusionCentralizerReceptive.
