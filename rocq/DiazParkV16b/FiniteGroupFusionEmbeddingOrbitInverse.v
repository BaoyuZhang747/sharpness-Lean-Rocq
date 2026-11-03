(** The actual inverse on raw subgroup maps, with literal evaluation and
    both cancellation laws. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionCentralizerMaps.
From DiazParkV16b Require Import FiniteGroupFusionEmbeddingOrbitMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionGroupIsomorphismMaps.
Local Open Scope group_scope.

Module DPFusionGroupIsomorphismInverse.
Section Maps.
Variables N T : finGroupType.
Variable e : {morphism [set: N] >-> T}.
Variable r : {morphism [set: T] >-> N}.
Hypothesis er : cancel e r.
Hypothesis re : cancel r e.

Definition unmap (P Q : {group N})
    (f : DPFusion.map (subgroup e P) (subgroup e Q)) : DPFusion.map P Q :=
  DPFusionSubgroup.reindex (subgroup_inverse er P) (subgroup_inverse er Q)
    (map re er f).

Lemma unmapE (P Q : {group N}) (f : DPFusion.map (subgroup e P) (subgroup e Q)) x :
  x \in P -> DPFusion.map_fun (unmap f) x = r (DPFusion.map_fun f (e x)).
Proof.
move=> hx; rewrite /unmap DPFusionSubgroup.reindexE mapE //.
rewrite -(er x); exact (subgroup_mem r (subgroup_mem e hx)).
Qed.

Lemma map_unmap (P Q : {group N}) (f : DPFusion.map (subgroup e P) (subgroup e Q)) :
  map er re (unmap f) = f.
Proof.
apply DPFusion.map_ext=> y hy.
rewrite (mapE er re (unmap f) hy) (unmapE f (subgroup_repr er hy)).
by rewrite !re.
Qed.

Lemma unmap_map (P Q : {group N}) (f : DPFusion.map P Q) :
  unmap (map er re f) = f.
Proof. apply DPFusion.map_ext=> x hx; by rewrite unmapE // map_imageE // er. Qed.

Lemma subgroup_sub (P Q : {group N}) :
  (subgroup e P \subset subgroup e Q) = (P \subset Q).
Proof.
apply/idP/idP.
- move=> h; apply/subsetP=> x hx.
  have hh := subgroup_repr er (subsetP h _ (subgroup_mem e hx)).
  by rewrite er in hh.
- exact: morphimS.
Qed.

Lemma subgroup_self_centralizing (P : {group N}) :
  ('C(subgroup e P) \subset subgroup e P) = ('C(P) \subset P).
Proof.
have h : (subgroup e 'C(P)%G : {set T}) = 'C(subgroup e P) :=
  congr1 (fun H : {group T} => (H : {set T})) (subgroup_centralizer er re P).
rewrite -h; exact (subgroup_sub 'C(P)%G P).
Qed.
End Maps.
End DPFusionGroupIsomorphismInverse.
