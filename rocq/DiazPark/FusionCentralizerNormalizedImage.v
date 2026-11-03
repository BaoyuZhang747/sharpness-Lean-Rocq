From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms
  GroupKNormalizer FusionCentralizerMaps FusionCentralizer FusionCentralizerAut
  FusionCentralizerReceptive FusionCentralizerCompression FusionCentralizerTransport.
Import DPFusion DPFusionSubgroup DPFusionCentralizer DPFusionAutomorphisms
  DPFusionCentralizerCompression DPFusionCentralizerTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerNormalizedImage.
Section Image.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Hypothesis abE : abelian E.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.
Variables (P : {group T}) (B : {group S}).
Variable theta : DPFusion.map (joint P) B.
Hypothesis htheta : DPFusionSystem.allowed F theta.
Hypothesis onto : DPFusion.image theta = B.
Variable g : DPFusion.map 'C(imageE theta)%G C.
Hypothesis hg : DPFusionSystem.allowed F g.
Hypothesis gfix : {in E, forall e, g (theta e) = e}.

Definition psi := DPFusion.compose theta (DPFusion.restrict g (image_joint_centralizes abE onto)).

Lemma psiE x : x \in joint P -> psi x = g (theta x).
Proof.
move=> Px; rewrite /psi DPFusion.compose_in // DPFusion.restrict_in //.
exact: DPFusion.map_into.
Qed.

Lemma psi_allowed : DPFusionSystem.allowed F psi.
Proof.
apply: (DPFusionSystem.composition_closed htheta).
exact: (DPFusionSystem.restriction_allowed _ hg).
Qed.

Lemma psi_fixes : {in E, psi =1 id}.
Proof. by move=> e Ee; rewrite psiE ?(subsetP (joint_right P) e Ee) // gfix. Qed.

Definition local_map : DPFusion.map P [set: T]%G :=
  lower (reindex (erefl (ambient P)) (esym (DPFusionCentralizerReceptive.ambient_top E))
    (DPFusion.restrict psi (joint_left P))).

Lemma local_mapE x : x \in P -> val (local_map x) = psi (val x).
Proof.
move=> Px; rewrite /local_map lowerE // reindexE DPFusion.restrict_in //.
exact: ambient_mem.
Qed.

Lemma local_map_allowed : DPFusionSystem.allowed (system F E) local_map.
Proof.
apply/allowedP; exists (reindex (erefl (joint P))
  (esym (DPFusionCentralizerReceptive.joint_top abE)) psi); split.
- exact: reindex_allowed psi_allowed.
- split.
  + by move=> x Px; rewrite reindexE local_mapE.
  + by move=> e Ee; rewrite reindexE psi_fixes.
Qed.

Lemma local_image :
  DPFusion.map_morphism psi @* ambient P = ambient (DPFusion.image local_map).
Proof.
apply/setP=> y; apply/idP/idP.
- move=> /morphimP[x _ /morphimP[z _ Pz ->] ->].
  change (psi (val z) \in ambient (DPFusion.image local_map)).
  rewrite -(local_mapE Pz); apply: ambient_mem; exact: DPFusion.image_mem Pz.
- move=> /morphimP[x _ /morphimP[z Pz _ ->] ->].
  change (val (local_map z) \in DPFusion.map_morphism psi @* ambient P).
  rewrite local_mapE //; apply: mem_morphim; first exact: subsetP (joint_left P) _ (ambient_mem Pz).
  exact: ambient_mem.
Qed.

Lemma compressed_image :
  DPFusion.map_morphism g @* imageP theta = ambient (DPFusion.image local_map).
Proof.
rewrite -local_image /imageP /=.
apply/setP=> y; apply/idP/idP.
- move=> /morphimP[x _ /morphimP[z _ Pz ->] ->].
  change (g (theta z) \in DPFusion.map_morphism psi @* ambient P).
  rewrite -(psiE (subsetP (joint_left P) z Pz)).
  exact: mem_morphim (subsetP (joint_left P) z Pz) Pz.
- move=> /morphimP[z _ Pz ->].
  change (psi z \in DPFusion.map_morphism g @* (DPFusion.map_morphism theta @* ambient P)).
  rewrite psiE ?(subsetP (joint_left P) z Pz) //.
  apply: mem_morphim.
  + exact: (subsetP (image_joint_centralizes abE onto) _
      (DPFusion.map_into theta (subsetP (joint_left P) z Pz))).
  + exact: mem_morphim (subsetP (joint_left P) z Pz) Pz.
Qed.

Lemma ambient_normalizer (U : {group T}) :
  (ambient 'N(U)%G : {set S}) = 'N_C(ambient U).
Proof.
change (sgval @* 'N(U) = C :&: 'N(sgval @* U)).
have hK : 'ker (@sgval S C) \subset U by rewrite ker_sgval sub1G.
by rewrite (morphim_normG hK (subsetT U)) im_sgval.
Qed.

Lemma compressed_normalizer_image :
  DPFusion.map_morphism g @* transported_normalizer F theta \subset
    ambient 'N(DPFusion.image local_map)%G.
Proof.
rewrite ambient_normalizer; apply/subsetIP; split.
- exact: subset_trans (morphimS _ (transported_normalizer_centralizes F theta)) (DPFusion.image_sub g).
- rewrite -compressed_image.
  exact: (morphim_norms (DPFusion.map_morphism g) (transported_normalizer_normalizes F theta)).
Qed.

Lemma transported_normalizer_card :
  (#|transported_normalizer F theta| <= #|'N(DPFusion.image local_map)|)%N.
Proof.
have h := subset_leq_card compressed_normalizer_image.
rewrite (card_injm (DPFusion.map_injm g) (transported_normalizer_centralizes F theta)) in h.
change (is_true (#|transported_normalizer F theta| <= #|sgval @* 'N(DPFusion.image local_map)|)%N) in h.
by rewrite (card_injm (injm_sgval _) (subsetT _)) in h.
Qed.

End Image.
End DPFusionCentralizerNormalizedImage.


