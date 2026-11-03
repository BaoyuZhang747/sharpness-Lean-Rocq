(** Native augmented exactness of every actual first-entry structured comma. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import NormalizerPointedSubgroups NormalizerOrbitPointedFirstComma
  NormalizerOrbitPointedFirstTerminal NormalizerOrbitPointedFirstCoreflection
  CategoryStringTerminalExact CategoryStringExactnessTransport CategoryInducedBarCofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPNormalizerOrbitPointedFirstExact.
Theorem first_under_augmented_exact (S : finGroupType) (F : DPFusionSystem.system S)
    (p : nat) (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (P : DPFusionOrbit.centric_object F)
    (B : DPNormalizerPointedSubgroups.pointed_category P) (R : pzRingType) :
  category_string_augmented_exact R (DPNormalizerOrbitPointedFirstComma.first_under B).
Proof.
apply (@DPCategoryStringExactnessTransport.exact_right_of_adjunction R
  (DPNormalizerOrbitPointedFirstComma.first_under B)
  (DPNormalizerOrbitPointedFirstComma.first_points B)
  (DPNormalizerOrbitPointedFirstCoreflection.first_coreflection pS sat B)
  (DPNormalizerOrbitPointedFirstComma.points_inclusion B)
  (DPNormalizerOrbitPointedFirstCoreflection.first_coreflection_adjunction pS sat B)).
exact (DPCategoryStringTerminalExact.terminal_augmented_exact
  (DPNormalizerOrbitPointedFirstTerminal.first_points_terminal B) R).
Qed.
End DPNormalizerOrbitPointedFirstExact.

