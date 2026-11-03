(** Actual comma of first-entry evaluation and its explicit isomorphism-pointed objects. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainNormalizer
  NormalizerOrbitPairCategory NormalizerOrbitCommaImageObjects NormalizerOrbitPointedFirst
  NormalizerPointedSubgroups NormalizerPointedSubgroupObjectEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains.
Local Open Scope group_scope.

Module DPNormalizerOrbitPointedFirstComma.
Section Comma.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : DPFusionOrbit.centric_object F.
Local Notation CP := (DPNormalizerOrbitCommaImage.pointed_category P).
Local Notation SP := (DPNormalizerPointedSubgroups.pointed_category P).
Local Notation E := (DPNormalizerOrbitPointedFirst.first_functor P).
Variable B : SP.
Definition first_under : category := structured_category E B.

Record first_point := {
  point_chain : CP;
  point_iso : @isomorphism SP B (fobj E point_chain)
}.

Definition point_under (Y : first_point) : first_under :=
  @Build_costructured_object (opposite CP) (opposite SP) (functor_op E) B
    (point_chain Y) (iso_hom (point_iso Y)).

Definition first_points : category.
Proof.
refine (@Build_category first_point (fun X Y => hom first_under (point_under X) (point_under Y))
  (fun X => Category.identity (point_under X)) (fun X Y Z f g => Category.compose f g) _ _ _).
- intros; apply compose_id_left.
- intros; apply compose_id_right.
- intros; apply compose_assoc.
Defined.

Lemma first_under_hom_unique (X Y : first_under) (f g : hom first_under X Y) : f = g.
Proof.
apply costructured_hom_ext; apply DPNormalizerOrbitCommaImage.pointed_source_hom_unique.
Qed.

Definition points_inclusion : functor first_points first_under.
Proof. refine (@Build_functor first_points first_under point_under (fun _ _ f => f) _ _); reflexivity. Defined.

Definition singleton_centric : DPFusionOrbit.centric_object F :=
  Sub (DPNormalizerPointedSubgroups.subgroup B) (DPNormalizerPointedSubgroups.subgroup_centric B).

Lemma singleton_normalizes : val (DPNormalizerPointedSubgroups.acting B) \subset
  DPNormalizerChain.normalizer (singleton singleton_centric).
Proof.
apply/subsetP=> x hx; apply/DPNormalizerChain.normalizerP=> i.
rewrite /subgroup singleton_entry; exact: subsetP (DPNormalizerPointedSubgroups.normalizes B) _ hx.
Qed.

Definition singleton_pair : DPNormalizerOrbitPair.pair_category F :=
  Sub (DPNormalizerPointedSubgroups.acting B, singleton singleton_centric) singleton_normalizes.

Definition singleton_point : CP :=
  @DPNormalizerOrbitCommaImage.Build_pointed_object S F P singleton_pair
    (DPNormalizerPointedSubgroups.point B).

Lemma singleton_first : fobj E singleton_point = B.
Proof.
change (DPNormalizerOrbitPointedFirst.first_object singleton_point = B).
rewrite /DPNormalizerOrbitPointedFirst.first_object /singleton_point /singleton_pair /singleton_centric.
rewrite -[RHS](DPNormalizerPointedSubgroupObjectEquality.object_eta B).
apply DPNormalizerPointedSubgroupObjectEquality.fixed_point_object_eq.
apply val_inj; by rewrite /bottom singleton_entry.
Qed.

Definition singleton_first_iso : @isomorphism SP B (fobj E singleton_point).
Proof. rewrite singleton_first; exact (iso_refl B). Defined.

Definition terminal_point : first_points := @Build_first_point singleton_point singleton_first_iso.
End Comma.
End DPNormalizerOrbitPointedFirstComma.
