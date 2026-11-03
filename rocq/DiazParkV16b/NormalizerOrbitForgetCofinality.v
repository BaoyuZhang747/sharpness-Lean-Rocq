(** All actual q-comma contractions, from first-entry images and strict prefixes. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryComma FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import NormalizerOrbitPairCategory NormalizerOrbitCommaImageObjects
  NormalizerOrbitCommaImageExact NormalizerOrbitPointedFirst NormalizerOrbitPointedFirstExact
  NormalizerPointedSubgroups NormalizerPointedSubgroupsExact CategoryStringExactnessTransport
  CategoryInducedBarCofinality CategoryQuillenA.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPNormalizerOrbitForgetCofinality.
Section Cofinality.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : pzRingType.

Theorem pointed_chains_augmented_exact (P : DPFusionOrbit.centric_object F) :
  category_string_augmented_exact R (DPNormalizerOrbitCommaImage.pointed_category P).
Proof.
apply (@DPCategoryStringExactnessTransport.exact_of_quasi_isomorphism R
  (DPNormalizerOrbitCommaImage.pointed_category P)
  (DPNormalizerPointedSubgroups.pointed_category P)
  (DPNormalizerOrbitPointedFirst.first_functor P)).
- apply DPCategoryQuillenA.structured_chain_quasi_isomorphism.
  exact (fun B => @DPNormalizerOrbitPointedFirstExact.first_under_augmented_exact S F p pS sat P B R).
- exact (DPNormalizerPointedSubgroupsExact.pointed_subgroups_augmented_exact P R).
Qed.

Theorem forget_comma_augmented_exact (P : DPFusionOrbit.centric_object F) :
  category_string_augmented_exact R (structured_category (DPNormalizerOrbitPair.forget F) P).
Proof.
apply DPNormalizerOrbitCommaImageExact.under_exact_of_pointed.
exact: pointed_chains_augmented_exact.
Qed.
End Cofinality.
End DPNormalizerOrbitForgetCofinality.
