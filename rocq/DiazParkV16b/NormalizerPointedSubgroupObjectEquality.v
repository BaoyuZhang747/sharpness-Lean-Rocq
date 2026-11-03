(** Equality for fixed acting group and point, retaining literal subgroup equality. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import NormalizerPointedSubgroups.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPNormalizerPointedSubgroupObjectEquality.
Lemma object_eta (S : finGroupType) (F : DPFusionSystem.system S)
    (P : DPFusionOrbit.centric_object F) (A : DPNormalizerPointedSubgroups.object P) :
  @DPNormalizerPointedSubgroups.Build_object S F P
    (DPNormalizerPointedSubgroups.acting A) (DPNormalizerPointedSubgroups.point A)
    (DPNormalizerPointedSubgroups.subgroup A) (DPNormalizerPointedSubgroups.subgroup_centric A)
    (DPNormalizerPointedSubgroups.normalizes A) = A.
Proof. by case: A. Qed.

Lemma fixed_point_object_eq (S : finGroupType) (F : DPFusionSystem.system S)
    (P A : DPFusionOrbit.centric_object F)
    (e : @isomorphism (DPFusionOrbit.centric_orbit_category F) P A)
    (Q R : {group S}) (cQ : DPFusionSystem.centric F Q) (cR : DPFusionSystem.centric F R)
    (nQ : val A \subset 'N(Q)) (nR : val A \subset 'N(R)) (h : Q = R) :
  @DPNormalizerPointedSubgroups.Build_object S F P A e Q cQ nQ =
  @DPNormalizerPointedSubgroups.Build_object S F P A e R cR nR.
Proof. subst R; f_equal; apply Prop_irrelevance. Qed.
End DPNormalizerPointedSubgroupObjectEquality.
