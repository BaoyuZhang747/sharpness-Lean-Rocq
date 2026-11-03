From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionCentralizerMaps FusionCentralizer.
Import DPFusion DPFusionSubgroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerAmbient.
Section Ambient.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Local Notation T := [subg 'C(E)]%type.

Lemma lift_allowed (P Q : {group T}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed (DPFusionCentralizer.system F E) f ->
  DPFusionSystem.allowed F (DPFusionSubgroup.lift f).
Proof.
move/DPFusionCentralizer.allowedP=> [fhat [hf [hext hfix]]].
pose g := DPFusion.restrict fhat (DPFusionCentralizer.joint_left P).
have hg := DPFusionSystem.restriction_allowed (DPFusionCentralizer.joint_left P) hf.
have sI : DPFusion.image g \subset ambient Q.
  apply/subsetP=> z /morphimP[x Px _ ->].
  have /morphimP[y _ Py ex] := Px.
  rewrite ex; change (g (val y) \in ambient Q).
  rewrite /g DPFusion.restrict_in ?ambient_mem // hext //.
  exact: ambient_mem (DPFusion.map_into f Py).
have h := DPFusionSystem.corestriction_allowed sI hg.
have e : DPFusion.corestrict sI = DPFusionSubgroup.lift f.
  apply: DPFusion.map_ext=> x /morphimP[y _ Py ->].
  rewrite DPFusion.corestrict_in ?ambient_mem //.
  rewrite /g DPFusion.restrict_in ?ambient_mem //.
  by rewrite hext // DPFusionSubgroup.liftE.
by rewrite e in h.
Qed.
End Ambient.
End DPFusionCentralizerAmbient.

