(** Actual subgroup and normalizer sharpness: unchanged pages, new vanishing input. *)
From Stdlib Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup all_classical reals topology.
From DiazPark Require Import Category CategoryModules FusionSystems FusionSaturation.
From DiazParkV16b Require Import LinkingSystem SingularCochainFilteredCollapse
 LinkingSubgroupRealizationComparison LinkingSubgroupGeometricSpectralSequence
 NormalizerLinkingRealizationSharpness NormalizerLinkingGeometricSpectralSequence.
From DiazParkV28 Require Import LinkingSubgroupRouteB NormalizerSharpnessRouteB.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV28LinkingSharpnessCollapse.
Section Collapse.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable K : fieldType.
Variable charp : p \in [pchar K].
Variable A : lmodType K.
Local Notation hSub := (@DPV28LinkingSubgroup.field_positive_limits Real S F L p hS sat K charp A).
Local Notation hNorm := (@DPV28NormalizerSharpness.field_positive_limits Real S F L p hS sat K charp A).

Theorem subgroup_later_positive_zero r i n
    (x : @DPLinkingSubgroupGeometricSpectralSequence.subgroup_page Real S F L K A
      r.+1 (Z.of_nat i.+1) n) : x = 0.
Proof. exact: (@singular_filtered_later_positive_zero Real K A _ _ hSub r i n x). Qed.

Theorem subgroup_later_d_zero r i n
    (x : @DPLinkingSubgroupGeometricSpectralSequence.subgroup_page Real S F L K A
      r.+1 (Z.of_nat i) n) :
  @DPLinkingSubgroupGeometricSpectralSequence.subgroup_d Real S F L K A
    r.+1 (Z.of_nat i) n x = 0.
Proof. exact: (@singular_filtered_later_d_zero Real K A _ _ hSub r i n x). Qed.

Definition subgroup_zero_column_back_iso r n := singular_filtered_zero_column_back_iso hSub r n.

Theorem subgroup_collapses_onto_vertical_axis :
  (forall r i n (x : @DPLinkingSubgroupGeometricSpectralSequence.subgroup_page Real S F L K A
    r.+1 (Z.of_nat i.+1) n), x = 0) /\
  (forall r i n (x : @DPLinkingSubgroupGeometricSpectralSequence.subgroup_page Real S F L K A
    r.+1 (Z.of_nat i) n),
    @DPLinkingSubgroupGeometricSpectralSequence.subgroup_d Real S F L K A
      r.+1 (Z.of_nat i) n x = 0).
Proof. split; [exact: subgroup_later_positive_zero | exact: subgroup_later_d_zero]. Qed.

Theorem normalizer_later_positive_zero r i n
    (x : @DPNormalizerLinkingGeometricSpectralSequence.normalizer_page Real S F L K A
      r.+1 (Z.of_nat i.+1) n) : x = 0.
Proof. exact: (@singular_filtered_later_positive_zero Real K A _ _ hNorm r i n x). Qed.

Theorem normalizer_later_d_zero r i n
    (x : @DPNormalizerLinkingGeometricSpectralSequence.normalizer_page Real S F L K A
      r.+1 (Z.of_nat i) n) :
  @DPNormalizerLinkingGeometricSpectralSequence.normalizer_d Real S F L K A
    r.+1 (Z.of_nat i) n x = 0.
Proof. exact: (@singular_filtered_later_d_zero Real K A _ _ hNorm r i n x). Qed.

Definition normalizer_zero_column_back_iso r n := singular_filtered_zero_column_back_iso hNorm r n.

Theorem normalizer_collapses_onto_vertical_axis :
  (forall r i n (x : @DPNormalizerLinkingGeometricSpectralSequence.normalizer_page Real S F L K A
    r.+1 (Z.of_nat i.+1) n), x = 0) /\
  (forall r i n (x : @DPNormalizerLinkingGeometricSpectralSequence.normalizer_page Real S F L K A
    r.+1 (Z.of_nat i) n),
    @DPNormalizerLinkingGeometricSpectralSequence.normalizer_d Real S F L K A
      r.+1 (Z.of_nat i) n x = 0).
Proof. split; [exact: normalizer_later_positive_zero | exact: normalizer_later_d_zero]. Qed.
End Collapse.
End DPV28LinkingSharpnessCollapse.
