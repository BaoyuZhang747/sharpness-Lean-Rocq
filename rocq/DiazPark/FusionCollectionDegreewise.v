(** Fixed-degree module isomorphisms for sufficient centric collections,
    including degree zero and the literal central-quotient collection. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  CategoryAtomicDeletionCore CategoryAtomicDeletionFiltration CategoryAtomicDeletionTheorem
  CategoryAtomicDeletionDegreewise HomologicalModuleIso BarHigherLimitVanishing
  FusionSystems FusionSaturation FusionOrbit FusionFiniteCategory BurnsideFusionRanks
  FusionRadical FusionAtomicConjugacyVanishing FusionCollectionAcyclicity
  FusionCollectionRestrictionAdapter FusionQuotientMaps FusionQuotientCollection
  FusionQuotientCollectionClosure FusionQuotientRadical.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPFusionFinite DPBurnsideFusionRanks
  DPFusionCollectionAcyclicity DiazParkHomologicalModuleIso DiazParkBarHigherLimitVanishing.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionCollectionDegreewise.
Section Collection.
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

Lemma outside_atomic_zero (q : centric_object F) :
  ~ H (val q) -> forall D : module_codiagram R (centric_orbit_category F),
    @coefficient_atomic (centric_finite_category F) R D q -> derived_all_zero D.
Proof.
move=> hq D hD.
apply: (@DPFusionAtomicConjugacyVanishing.nonradical_atomic_zero S F p pS sat R q _ D hD).
move=> hr; apply hq; exact: Hradical (valP q) hr.
Qed.

Definition collection_derived_iso (D : module_codiagram R (centric_orbit_category F)) n :
  @isomorphism (module_category R) (derived_limit R D n)
    (derived_limit R (fobj (collection_restriction F H R) D) n) :=
  @finite_collection_derived_iso (centric_finite_category F)
    (@centric_rank S F) (@centric_rank_le S F) (@centric_rank_equal_related S F)
    R (@centric_collection S F H) (@centric_collection_upward S F H Hconj Hover)
    outside_atomic_zero D n.

Theorem collection_degreewise_zero_iff
    (D : module_codiagram R (centric_orbit_category F)) n :
  (forall q : derived_limit R D n, q = 0) <->
  (forall q : derived_limit R (fobj (collection_restriction F H R) D) n, q = 0).
Proof. exact: module_iso_zero_iff (collection_derived_iso D n). Qed.
End Collection.

Section LiteralCollection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis pZ : p.-group Z.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : pzRingType.
Local Notation H := (fun P : {group S} => is_true (DPFusionQuotientCollection.collection cZ P)).

Definition literal_collection_derived_iso
    (D : module_codiagram R (centric_orbit_category F)) n :
  @isomorphism (module_category R) (derived_limit R D n)
    (derived_limit R (DPFusionCollectionAdapter.literal_restriction cZ D) n) :=
  module_iso_comp
    (@collection_derived_iso S F p pS sat H
      (@DPFusionQuotientCollectionClosure.collection_conjugate S F Z cZ)
      (@DPFusionQuotientCollectionClosure.collection_overgroup S F Z cZ)
      (@DPFusionQuotientRadical.centric_radical_collection S F Z cZ p pZ) R D n)
    (DPFusionCollectionAdapter.restriction_adapter_iso cZ D n).

Theorem literal_collection_degreewise_zero_iff
    (D : module_codiagram R (centric_orbit_category F)) n :
  (forall q : derived_limit R D n, q = 0) <->
  (forall q : derived_limit R (DPFusionCollectionAdapter.literal_restriction cZ D) n, q = 0).
Proof. exact: module_iso_zero_iff (literal_collection_derived_iso D n). Qed.
End LiteralCollection.
End DPFusionCollectionDegreewise.
