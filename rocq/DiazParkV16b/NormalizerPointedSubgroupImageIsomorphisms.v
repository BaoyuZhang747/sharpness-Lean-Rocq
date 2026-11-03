(** A full image yields an actual inverse in the pointed subgroup category. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import NormalizerPointedSubgroups NormalizerPointedSubgroupObjectEquality
  NormalizerPointedSubgroupImageFactorization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPNormalizerPointedSubgroups DPNormalizerPointedSubgroupImageFactorization.

Module DPNormalizerPointedSubgroupImageIsomorphisms.
Section ImageIso.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : DPFusionOrbit.centric_object F.
Local Notation C := (pointed_category P).
Variables A B : C.
Variable f : hom C A B.
Hypothesis he : arrow_image f = subgroup B.

Lemma full_image_object : image_object f = B.
Proof.
rewrite -[RHS](DPNormalizerPointedSubgroupObjectEquality.object_eta B).
apply DPNormalizerPointedSubgroupObjectEquality.fixed_point_object_eq; exact he.
Qed.

Definition full_image_iso : @isomorphism C A B.
Proof. rewrite -full_image_object; exact (image_iso f). Defined.

Lemma full_image_iso_hom : iso_hom full_image_iso = f.
Proof. exact: hom_unique. Qed.
End ImageIso.
End DPNormalizerPointedSubgroupImageIsomorphisms.
