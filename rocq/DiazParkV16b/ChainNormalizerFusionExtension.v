(** The actual minimal-join extension predicate for a centric chain. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionCentricBasics.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainNormalizer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerChain.
Local Open Scope group_scope.

Module DPChainNormalizerFusion.
Section Extensions.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.

Definition join_subgroup (P : {group S}) : {group S} := (val (top c) <*> P)%G.
Lemma top_sub_join (P : {group S}) : val (top c) \subset join_subgroup P.
Proof. exact: joing_subl. Qed.
Lemma acting_sub_join (P : {group S}) : P \subset join_subgroup P.
Proof. exact: joing_subr. Qed.
Lemma entry_sub_join (P : {group S}) (i : 'I_(length c).+1) : subgroup c i \subset join_subgroup P.
Proof. exact: subset_trans (@entry_sub_top S F c i) (top_sub_join P). Qed.
Lemma join_centric (P : {group S}) : DPFusionSystem.centric F (join_subgroup P).
Proof. exact: DPFusionCentricBasics.centric_overgroup (top_sub_join P) (valP (top c)). Qed.
Definition join_object (P : {group S}) : DPFusionOrbit.centric_object F :=
  Sub (join_subgroup P) (join_centric P).
Lemma join_normalizes_top (P : {group S}) (hP : P \subset normalizer c) :
  join_subgroup P \subset 'N(val (top c)).
Proof.
apply/joing_subP; split; first exact: normG.
exact: subset_trans hP (normalizer_sub_top c).
Qed.

Definition preserves_chain (P Q : {group S}) (b : DPFusion.map (join_subgroup P) (join_subgroup Q)) :=
  [forall i : 'I_(length c).+1,
    DPFusion.image (DPFusion.restrict b (entry_sub_join P i)) == subgroup c i].
Lemma preserves_chainP (P Q : {group S}) (b : DPFusion.map (join_subgroup P) (join_subgroup Q)) :
  reflect (forall i, DPFusion.image (DPFusion.restrict b (entry_sub_join P i)) = subgroup c i)
    (preserves_chain b).
Proof.
apply: (iffP forallP).
- move=> h i; exact: eqP (h i).
- move=> h i; exact/eqP.
Qed.

Definition normalizer_extension (P Q : {group S}) (f : DPFusion.map P Q) :=
  [exists b : DPFusion.map (join_subgroup P) (join_subgroup Q),
    DPFusionSystem.allowed F b && preserves_chain b && [forall x in P, b x == f x]].

Lemma normalizer_extensionP (P Q : {group S}) (f : DPFusion.map P Q) : reflect
  (exists b : DPFusion.map (join_subgroup P) (join_subgroup Q),
    DPFusionSystem.allowed F b /\
    (forall i, DPFusion.image (DPFusion.restrict b (entry_sub_join P i)) = subgroup c i) /\
    {in P, b =1 f}) (normalizer_extension f).
Proof.
apply: (iffP existsP).
- move=> [b /andP[/andP[hb /preserves_chainP hc] /forall_inP hf]].
  exists b; split=> //; split=> // x hx; exact: eqP (hf x hx).
- move=> [b [hb [hc hf]]]; exists b; apply/andP; split.
  + apply/andP; split=> //; exact/preserves_chainP.
  + apply/forall_inP=> x hx; apply/eqP; exact: hf.
Qed.

Lemma extension_value_in_entry (P Q : {group S})
    (b : DPFusion.map (join_subgroup P) (join_subgroup Q)) : preserves_chain b ->
  forall i x, x \in subgroup c i -> b x \in subgroup c i.
Proof.
move/preserves_chainP=> hb i x hx.
have him := DPFusion.image_mem (DPFusion.restrict b (entry_sub_join P i)) hx.
by rewrite hb DPFusion.restrict_in // in him.
Qed.

Theorem normalizer_extension_allowed (P Q : {group S}) (f : DPFusion.map P Q) :
  normalizer_extension f -> DPFusionSystem.allowed F f.
Proof.
move/normalizer_extensionP=> [b [hb [hc hf]]].
pose r := DPFusion.restrict b (acting_sub_join P).
have hr : DPFusion.image r \subset Q.
  apply/subsetP=> y /morphimP[x _ hx ->].
  rewrite DPFusion.map_morphismE /r DPFusion.restrict_in // hf //.
  exact: DPFusion.map_into hx.
have he : DPFusion.corestrict hr = f.
  apply DPFusion.map_ext=> x hx.
  by rewrite DPFusion.corestrict_in // /r DPFusion.restrict_in // hf.
rewrite -he; apply: DPFusionSystem.corestriction_allowed.
exact: DPFusionSystem.restriction_allowed hb.
Qed.

End Extensions.
End DPChainNormalizerFusion.
