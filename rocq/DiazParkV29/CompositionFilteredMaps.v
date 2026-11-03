(** Full transfer and restriction compatibility of the actual colimit.
    Conjugation is the transfer along an orbit isomorphism. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  MackeyStructures MackeySubquotients MackeyModuleCarriers MackeyModuleMaps
  MackeyBarReduction FusionSystems FusionOrbit FusionMackeyShape.
From DiazParkV29 Require Import FilteredLimitsDirected FilteredLimitsMaps
  FilteredLimitsDiagrams CompositionFilteredMackey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits DPFilteredMaps DPFilteredDiagrams
  DPFilteredLimitsMackey.
Local Open Scope ring_scope.

Module DPFilteredMackeyMaps.
Section FullMaps.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).
Let L := functor_id (DPFusionOrbit.orbit_category F).
Let D := finite_diagram M L.

Definition transfer_family P Q (f : DPFusionOrbit.orbit_hom F P Q) i :
    {linear dm_value (pointwise_system D P) i -> dm_value (pointwise_system D Q) i} :=
  mackey_push (subfunctor_mackey (finite_value i)) f.

Lemma transfer_family_natural P Q (f : DPFusionOrbit.orbit_hom F P Q) i j
    (h : stage_le i j) x :
    transfer_family f j (dm_map (pointwise_system D P) h x) =
    dm_map (pointwise_system D Q) h (transfer_family f i x).
Proof. apply: submodule_val_injective; reflexivity. Qed.

Definition colimit_transfer P Q (f : DPFusionOrbit.orbit_hom F P Q) :
    {linear colimit_module (pointwise_system D P) -> colimit_module (pointwise_system D Q)} :=
  module_hom_to_linear (exist _ (direct_limit_map (transfer_family f))
    (@direct_limit_map_linear R (finite_poset M) (pointwise_system D P) (pointwise_system D Q)
      (transfer_family f) (@transfer_family_natural P Q f))).

Lemma colimit_transfer_in P Q (f : DPFusionOrbit.orbit_hom F P Q) i
    (x : dm_value (pointwise_system D P) i) :
    colimit_transfer f (colimit_in x) = colimit_in (V := pointwise_system D Q) (i := i) (mackey_push (subfunctor_mackey (finite_value i)) f x).
Proof. exact (@direct_limit_map_in R (finite_poset M) (pointwise_system D P) (pointwise_system D Q) (transfer_family f) (@transfer_family_natural P Q f) i x). Qed.

Theorem colimit_transfer_ambient P Q (f : DPFusionOrbit.orbit_hom F P Q)
    (x : colimit_module (pointwise_system D P)) :
    module_hom_fun (component (colimit_to_ambient M L) Q) (colimit_transfer f x) =
      mackey_push M f (module_hom_fun (component (colimit_to_ambient M L) P) x).
Proof.
have [i [v <-]] := colimit_in_surjective x.
rewrite colimit_transfer_in !colimit_to_ambient_in; reflexivity.
Qed.

Theorem colimit_restriction_ambient P Q (f : DPFusionOrbit.orbit_hom F P Q)
    (x : colimit_module (pointwise_system D Q)) :
    module_hom_fun (component (colimit_to_ambient M L) P) (pointwise_arrow D f x) =
      mackey_pull M f (module_hom_fun (component (colimit_to_ambient M L) Q) x).
Proof.
have [i [v <-]] := colimit_in_surjective x.
rewrite pointwise_arrow_in !colimit_to_ambient_in; reflexivity.
Qed.

Theorem colimit_conjugation_ambient P Q
    (e : @isomorphism (DPFusionOrbit.orbit_category F) P Q)
    (x : colimit_module (pointwise_system D P)) :
    module_hom_fun (component (colimit_to_ambient M L) Q) (colimit_transfer (iso_hom e) x) =
      mackey_push M (iso_hom e) (module_hom_fun (component (colimit_to_ambient M L) P) x).
Proof. exact: colimit_transfer_ambient. Qed.
End FullMaps.
End DPFilteredMackeyMaps.

Print Assumptions DPFilteredMackeyMaps.colimit_transfer_ambient.
Print Assumptions DPFilteredMackeyMaps.colimit_restriction_ambient.



