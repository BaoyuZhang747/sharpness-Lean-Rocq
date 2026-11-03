From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms
  FusionCentralizerMaps FusionCentralizer FusionCentralizerExtension FusionCentralizerAut.
Import DPFusion DPFusionSubgroup DPFusionAutomorphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerAutRestriction.
Import DPFusionCentralizerAut.

Section Restriction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.
Local Notation J P := (DPFusionCentralizer.joint (E := E) P).
Local Notation CF := (DPFusionCentralizer.system F E).
Variable P : {group T}.

Lemma joint_aut_of_K (a : {perm S}) : a \in K F E P -> a \in Aut (J P).
Proof.
move=> Ka; apply: (subsetP (DPFusionSaturation.aut_group_sub F (J P))).
exact: subsetP (K_sub F E P) a Ka.
Qed.

Lemma restricted_image (a : {perm S}) (Ka : a \in K F E P) :
  DPFusion.image (DPFusion.restrict (aut_to_map (joint_aut_of_K Ka))
    (DPFusionCentralizer.joint_left P)) \subset ambient P.
Proof.
apply/subsetP=> y /morphimP[x Px _ ->].
rewrite DPFusion.map_morphismE DPFusion.restrict_in // aut_to_mapE.
- exact: (@K_preserves S F E P a Ka x Px).
- exact: subsetP (DPFusionCentralizer.joint_left P) x Px.
Qed.

Definition raw_restriction (a : {perm S}) (Ka : a \in K F E P) : DPFusion.map P P :=
  lower (DPFusion.corestrict (restricted_image Ka)).

Lemma raw_restrictionE (a : {perm S}) (Ka : a \in K F E P) (x : T) :
  x \in P -> val (raw_restriction Ka x) = a (val x).
Proof.
move=> Px; rewrite /raw_restriction lowerE //.
rewrite DPFusion.corestrict_in ?ambient_mem // DPFusion.restrict_in ?ambient_mem //.
apply: aut_to_mapE.
exact: subsetP (DPFusionCentralizer.joint_left P) _ (ambient_mem Px).
Qed.

Lemma raw_restriction_allowed (a : {perm S}) (Ka : a \in K F E P) :
  DPFusionSystem.allowed CF (raw_restriction Ka).
Proof.
apply/DPFusionCentralizer.allowedP; exists (aut_to_map (joint_aut_of_K Ka)); split.
- apply: aut_to_map_allowed; exact: subsetP (K_sub F E P) a Ka.
- split.
  + move=> x Px; rewrite raw_restrictionE // aut_to_mapE //.
    exact: subsetP (DPFusionCentralizer.joint_left P) _ (ambient_mem Px).
  + move=> e Ee; rewrite aut_to_mapE; first exact: (@K_fixes S F E P a Ka e Ee).
    exact: subsetP (DPFusionCentralizer.joint_right P) e Ee.
Qed.

Definition restriction (a : {perm S}) : {perm T} :=
  map_aut (raw_restriction (valP (subg (K F E P) a))).

Lemma restriction_mem (a : {perm S}) : restriction a \in DPFusionSaturation.aut_group CF P.
Proof. apply: map_aut_allowed; exact: raw_restriction_allowed. Qed.

Lemma restriction_Aut (a : {perm S}) : restriction a \in Aut P.
Proof. exact: subsetP (DPFusionSaturation.aut_group_sub CF P) _ (restriction_mem a). Qed.

Lemma restrictionE (a : {perm S}) :
  a \in K F E P -> forall x : T, x \in P -> val (restriction a x) = a (val x).
Proof.
move=> Ka x Px; rewrite /restriction map_autE // raw_restrictionE //.
by rewrite subgK.
Qed.

Lemma restriction_morphM :
  {in K F E P &, {morph restriction : a b / a * b}}.
Proof.
move=> a b Ka Kb.
apply: (eq_Aut (restriction_Aut _) (groupM (restriction_Aut a) (restriction_Aut b)))=> x Px.
apply: val_inj; rewrite permM restrictionE ?groupM //.
have Pxa : restriction a x \in P := Aut_closed (restriction_Aut a) Px.
by rewrite restrictionE // restrictionE // permM.
Qed.

Canonical restriction_morphism := Morphism restriction_morphM.

Lemma restriction_injective : 'injm restriction_morphism.
Proof.
apply/injmP=> a b Ka Kb eab.
apply: (eq_Aut (joint_aut_of_K Ka) (joint_aut_of_K Kb))=> x Jx.
have hx : x \in ambient P * E by move: Jx; rewrite DPFusionCentralizerExtension.joint_product.
case/mulsgP: hx=> y e Py Ee ->.
have Jy := subsetP (DPFusionCentralizer.joint_left P) y Py.
have Je := subsetP (DPFusionCentralizer.joint_right P) e Ee.
have eqy : a y = b y.
  have Pz := ambient_repr Py.
  have h := congr1 (fun c : {perm T} => val (c (subg C y))) eab.
  change (val (restriction a (subg C y)) = val (restriction b (subg C y))) in h.
  rewrite !restrictionE // (ambient_subgK Py) in h; exact h.
rewrite (morphicP (Aut_morphic (joint_aut_of_K Ka)) y e Jy Je).
rewrite (morphicP (Aut_morphic (joint_aut_of_K Kb)) y e Jy Je).
by rewrite eqy (@K_fixes S F E P a Ka e Ee) (@K_fixes S F E P b Kb e Ee).
Qed.

Lemma restriction_image_sub :
  restriction_morphism @* K F E P \subset DPFusionSaturation.aut_group CF P.
Proof. by apply/subsetP=> a /morphimP[b _ _ ->]; exact: restriction_mem. Qed.

Lemma restriction_surjective (b : {perm T}) :
  b \in DPFusionSaturation.aut_group CF P ->
  exists a : {perm S}, a \in K F E P /\ restriction a = b.
Proof.
move=> Fb.
have Ab := subsetP (DPFusionSaturation.aut_group_sub CF P) b Fb.
have Ff := aut_to_map_allowed Ab Fb.
case/DPFusionCentralizer.allowedP: Ff=> h [Fh [hext hfix]].
have Ah := map_aut_mem h.
have Fha := map_aut_allowed Fh.
have Kh : map_aut h \in K F E P.
  apply/setIdP; split; first exact Fha.
  apply/andP; split; apply/forall_inP=> x Px.
  - have Pz := ambient_repr Px.
    have Jx := subsetP (DPFusionCentralizer.joint_left P) x Px.
    rewrite map_autE // -(ambient_subgK Px) hext //.
    exact: ambient_mem (DPFusion.map_into (aut_to_map Ab) Pz).
  - apply/eqP; rewrite map_autE; first exact: hfix x Px.
    exact: subsetP (DPFusionCentralizer.joint_right P) x Px.
exists (map_aut h); split; first exact Kh.
apply: (eq_Aut (restriction_Aut _) Ab)=> x Px; apply: val_inj.
rewrite restrictionE // map_autE ?hext ?aut_to_mapE //.
exact: subsetP (DPFusionCentralizer.joint_left P) _ (ambient_mem Px).
Qed.

Lemma restriction_image :
  restriction_morphism @* K F E P = DPFusionSaturation.aut_group CF P.
Proof.
apply/eqP; rewrite eqEsubset restriction_image_sub /=.
apply/subsetP=> b Fb; case: (restriction_surjective Fb)=> a [Ka <-].
apply/morphimP; exists a=> //. 
Qed.

Lemma restriction_isom :
  isom (K F E P) (DPFusionSaturation.aut_group CF P) restriction_morphism.
Proof. by apply/isomP; split; [exact: restriction_injective | exact: restriction_image]. Qed.

End Restriction.
End DPFusionCentralizerAutRestriction.






