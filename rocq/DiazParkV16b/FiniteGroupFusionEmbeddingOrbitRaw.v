(** Fusion and centricity transport to the actual image subgroup carrier. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy FusionOrbit.
From DiazParkV16b Require Import FiniteGroupFusion FiniteGroupFusionEmbedding
  FiniteGroupFusionEmbeddingImage FiniteGroupFusionEmbeddingOrbitMaps
  FiniteGroupFusionEmbeddingOrbitInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion.
Local Open Scope group_scope.

Module DPFiniteGroupFusionEmbeddingOrbit.
Section Raw.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.
Local Notation T := [the finGroupType of [subg (DPFiniteGroupFusionEmbeddingImage.image_group E)]%type].
Local Notation e := (DPFiniteGroupFusionEmbeddingImage.image_equivalence E).
Local Notation r := (DPFiniteGroupFusionEmbeddingImage.image_inverse injE).
Local Notation er := (DPFiniteGroupFusionEmbeddingImage.image_equivalence_inverse injE).
Local Notation re := (DPFiniteGroupFusionEmbeddingImage.image_inverse_equivalence injE).
Local Notation F := (DPFiniteGroupFusionEmbedding.system E).
Local Notation H := (DPFiniteGroupFusion.system (DPFiniteGroupFusionEmbeddingImage.image_group E)).

Definition forward_subgroup := DPFusionGroupIsomorphismMaps.subgroup e.
Definition backward_subgroup := DPFusionGroupIsomorphismMaps.subgroup r.

Lemma forward_backward P : backward_subgroup (forward_subgroup P) = P.
Proof. exact (@DPFusionGroupIsomorphismMaps.subgroup_inverse N T e r er P). Qed.

Lemma backward_forward Q : forward_subgroup (backward_subgroup Q) = Q.
Proof. exact (@DPFusionGroupIsomorphismMaps.inverse_subgroupK N T e r re Q). Qed.

Lemma forward_mem (P : {group N}) x : x \in P -> e x \in forward_subgroup P.
Proof. exact: DPFusionGroupIsomorphismMaps.subgroup_mem. Qed.

Lemma forward_repr (P : {group N}) y : y \in forward_subgroup P -> r y \in P.
Proof. move=> hy; exact (@DPFusionGroupIsomorphismMaps.subgroup_repr N T e r er P y hy). Qed.

Definition forward_raw (P Q : {group N}) (f : DPFusion.map P Q) :=
  DPFusionGroupIsomorphismMaps.map er re f.
Definition backward_raw (P Q : {group N})
    (f : DPFusion.map (forward_subgroup P) (forward_subgroup Q)) :=
  DPFusionGroupIsomorphismInverse.unmap er re f.

Lemma forward_rawE (P Q : {group N}) (f : DPFusion.map P Q) x :
  x \in P -> forward_raw f (e x) = e (f x).
Proof. exact: DPFusionGroupIsomorphismMaps.map_imageE. Qed.

Lemma forward_raw_value (P Q : {group N}) (f : DPFusion.map P Q) y :
  y \in forward_subgroup P -> val (forward_raw f y) = E (f (r y)).
Proof. move=> hy; rewrite /forward_raw DPFusionGroupIsomorphismMaps.mapE //; reflexivity. Qed.

Lemma backward_rawE (P Q : {group N})
    (f : DPFusion.map (forward_subgroup P) (forward_subgroup Q)) x :
  x \in P -> E (backward_raw f x) = val (f (e x)).
Proof.
move=> hx; rewrite /backward_raw DPFusionGroupIsomorphismInverse.unmapE //.
exact (congr1 val (re (f (e x)))).
Qed.

Lemma forward_backward_raw (P Q : {group N})
    (f : DPFusion.map (forward_subgroup P) (forward_subgroup Q)) :
  forward_raw (backward_raw f) = f.
Proof. exact: DPFusionGroupIsomorphismInverse.map_unmap. Qed.

Lemma backward_forward_raw (P Q : {group N}) (f : DPFusion.map P Q) :
  backward_raw (forward_raw f) = f.
Proof. exact: DPFusionGroupIsomorphismInverse.unmap_map. Qed.

Lemma forward_allowed (P Q : {group N}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> DPFusionSystem.allowed H (forward_raw f).
Proof.
move/DPFiniteGroupFusionEmbedding.allowedP=> [g hg].
apply/DPFiniteGroupFusion.allowedP; exists g=> y hy.
rewrite forward_raw_value // hg ?forward_repr //.
have he := congr1 val (re y); exact (congr1 (fun z : G => z ^ g) he).
Qed.

Lemma backward_allowed (P Q : {group N})
    (f : DPFusion.map (forward_subgroup P) (forward_subgroup Q)) :
  DPFusionSystem.allowed H f -> DPFusionSystem.allowed F (backward_raw f).
Proof.
move/DPFiniteGroupFusion.allowedP=> [g hg].
apply/DPFiniteGroupFusionEmbedding.allowedP; exists g=> x hx.
by rewrite backward_rawE // hg ?forward_mem.
Qed.

Lemma forward_raw_image (P Q : {group N}) (f : DPFusion.map P Q) :
  DPFusion.image (forward_raw f) = forward_subgroup (DPFusion.image f).
Proof. exact: DPFusionGroupIsomorphismMaps.map_image. Qed.

Lemma forward_conjugate (P Q : {group N}) :
  DPFusionSystem.conjugate H (forward_subgroup P) (forward_subgroup Q) =
    DPFusionSystem.conjugate F P Q.
Proof.
apply/existsP/existsP.
- move=> [f /andP[hf /eqP ho]]; exists (backward_raw f).
  apply/andP; split; first exact: backward_allowed.
  apply/eqP; apply (DPFusionGroupIsomorphismMaps.subgroup_injective er).
  change (forward_subgroup (DPFusion.image (backward_raw f)) = forward_subgroup Q).
  by rewrite -forward_raw_image forward_backward_raw.
- move=> [f /andP[hf /eqP ho]]; exists (forward_raw f).
  apply/andP; split; first exact: forward_allowed.
  by apply/eqP; rewrite forward_raw_image ho.
Qed.

Lemma forward_centric (P : {group N}) :
  DPFusionSystem.centric H (forward_subgroup P) = DPFusionSystem.centric F P.
Proof.
apply/idP/idP.
- move=> hc; apply/forallP=> Q; apply/implyP=> hPQ.
  have h := implyP (forallP hc (forward_subgroup Q)).
  rewrite forward_conjugate in h.
  have hh := h hPQ.
  by rewrite (DPFusionGroupIsomorphismInverse.subgroup_self_centralizing er re) in hh.
- move=> hc; apply/forallP=> Q; apply/implyP=> hPQ.
  rewrite -(backward_forward Q) forward_conjugate in hPQ.
  have h := implyP (forallP hc (backward_subgroup Q)) hPQ.
  have hh := DPFusionGroupIsomorphismInverse.subgroup_self_centralizing er re (backward_subgroup Q).
  by rewrite -/(forward_subgroup _) backward_forward in hh; rewrite hh.
Qed.
End Raw.
End DPFiniteGroupFusionEmbeddingOrbit.
