(** Exact actual augmented strings of pointed normalized centric subgroups.
    This consumes the constructed join and its two actual natural transformations. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category FusionSystems FusionOrbit.
From DiazParkV16b Require Import NormalizerPointedSubgroups
  NormalizerPointedSubgroupsContraction CategoryStringConstantChains
  CategoryStringContraction CategoryInducedBarCofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPNormalizerPointedSubgroupsExact.
Section Exact.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : DPFusionOrbit.centric_object F.
Local Notation C := (DPNormalizerPointedSubgroups.pointed_category P).
Local Notation b := (DPNormalizerPointedSubgroupsContraction.base P).
Local Notation J := (DPNormalizerPointedSubgroupsContraction.join_functor P).

Definition constant_to_join : nat_trans
  (DPCategoryStringConstant.constant_functor C b) J.
Proof.
refine (@Build_nat_trans C C (DPCategoryStringConstant.constant_functor C b) J
  (DPNormalizerPointedSubgroupsContraction.base_to_join_component (P := P)) _).
intros; apply DPNormalizerPointedSubgroups.hom_unique.
Defined.

Theorem pointed_subgroups_augmented_exact (R : pzRingType) :
  category_string_augmented_exact R C.
Proof.
exact (@DPCategoryStringContraction.category_string_augmented_exact_of_contraction
  R C b J (DPNormalizerPointedSubgroupsContraction.join_unit P) constant_to_join).
Qed.
End Exact.
End DPNormalizerPointedSubgroupsExact.

Print Assumptions DPNormalizerPointedSubgroupsExact.pointed_subgroups_augmented_exact.
