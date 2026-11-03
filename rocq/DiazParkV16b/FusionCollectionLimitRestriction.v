(** Literal limit restriction to a sufficient centric collection.  The
    deletion-kernel acyclicity is supplied by the proved fusion theorem. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryAtomicDeletionCore CategoryAtomicDeletionDegreewise
  FusionSystems FusionOrbit FusionSaturation FusionRadical FusionFiniteCategory
  BurnsideFusionRanks FusionCollectionAcyclicity FusionCollectionDegreewise.
From DiazParkV16b Require Import CollectionLimitRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPFusionFinite DPBurnsideFusionRanks
  DPFusionCollectionAcyclicity DPCollectionLimitRestriction.
Local Open Scope group_scope.

Module DPFusionCollectionLimitRestriction.
Section Collection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Variable pS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable H : {group S} -> Prop.
Variable Hconj : forall P Q, DPFusionSystem.conjugate F P Q -> H P -> H Q.
Variable Hover : forall (P Q : {group S}), P \subset Q -> H P -> H Q.
Variable Hradical : forall P, DPFusionSystem.centric F P -> DPFusionRadical.radical F p P -> H P.
Variable R : pzRingType.
Variable D : module_codiagram R (centric_orbit_category F).

Definition sufficient_collection_limit_iso : @isomorphism (module_category R)
    (module_limit_type D) (module_limit_type (fobj (collection_restriction F H R) D)) :=
  @collection_limit_iso R (centric_orbit_category F) (@centric_collection S F H)
    (@centric_collection_upward S F H Hconj Hover) D
    (@deletion_kernel_all_cohomology_zero (centric_finite_category F)
      (@centric_rank S F) (@centric_rank_le S F) (@centric_rank_equal_related S F)
      R (@centric_collection S F H) (@centric_collection_upward S F H Hconj Hover)
      (@DPFusionCollectionDegreewise.outside_atomic_zero S F p pS sat H Hradical R) D 0)
    (@deletion_kernel_all_cohomology_zero (centric_finite_category F)
      (@centric_rank S F) (@centric_rank_le S F) (@centric_rank_equal_related S F)
      R (@centric_collection S F H) (@centric_collection_upward S F H Hconj Hover)
      (@DPFusionCollectionDegreewise.outside_atomic_zero S F p pS sat H Hradical R) D 1).

Theorem sufficient_collection_limit_component (v : module_limit_type D)
    (P : centric_object F) (hP : H (val P)) :
  module_limit_val (module_hom_fun (iso_hom sufficient_collection_limit_iso) v) (exist _ P hP) =
    module_limit_val v P.
Proof. exact: collection_limit_iso_component. Qed.

End Collection.
End DPFusionCollectionLimitRestriction.
