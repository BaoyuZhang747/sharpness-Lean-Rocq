(** Sufficient collections in an actual saturated centric orbit category.
    The nonradical atomic input is discharged by the proved comparison,
    normal-p reflection, and fusion-conjugacy transport. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryModules CategoryAtomicDeletionTheorem
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionRadical
  FusionAtomicConjugacyVanishing FusionCollectionAcyclicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCollection.
Section SaturatedCollection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable H : {group S} -> Prop.
Hypothesis Hconj : forall P Q, DPFusionSystem.conjugate F P Q -> H P -> H Q.
Hypothesis Hover : forall (P Q : {group S}), P \subset Q -> H P -> H Q.
Hypothesis Hradical : forall P, DPFusionSystem.centric F P ->
  DPFusionRadical.radical F p P -> H P.
Variable R : pzRingType.

Theorem collection_acyclic_iff
    (D : module_codiagram R (DPFusionOrbit.centric_orbit_category F)) :
  derived_positive_zero D <->
  derived_positive_zero
    (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D).
Proof.
apply: (@DPFusionCollectionAcyclicity.collection_acyclic_of_atomic_vanishing
  S F H Hconj Hover R p Hradical _ D).
exact: (@DPFusionAtomicConjugacyVanishing.nonradical_atomic_zero S F p pS sat R).
Qed.

Theorem collection_all_zero_iff
    (D : module_codiagram R (DPFusionOrbit.centric_orbit_category F)) :
  derived_all_zero D <->
  derived_all_zero
    (fobj (DPFusionCollectionAcyclicity.collection_restriction F H R) D).
Proof.
apply: (@DPFusionCollectionAcyclicity.collection_all_zero_of_atomic_vanishing
  S F H Hconj Hover R p Hradical _ D).
exact: (@DPFusionAtomicConjugacyVanishing.nonradical_atomic_zero S F p pS sat R).
Qed.

End SaturatedCollection.
End DPFusionCollection.
