(** Ordinary cohomology of a finite group is the actual compatible-family
    limit over its Sylow fusion system, with literal restriction components. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleProducts
  CategoryModuleLimits ModuleInfrastructure MackeyModuleCarriers
  HomologicalModuleIso FusionOrbit FusionStableElements FusionStableLimit.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyHomogeneousComparison
  GroupCohomologyOrbitCoefficient GroupCohomologyMackeyPair
  FiniteGroupFusion FiniteGroupFusionSubgroups FiniteGroupFusionSaturation
  GroupCohomologyStableElementsFusion GroupCohomologyStableElementsNative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyFunctor
  DPGroupCohomologyPullback DPGroupCohomologyHomogeneousComparison
  DPGroupCohomologyMackeyPair DPGroupCohomologyStableElementsFusion
  DPGroupCohomologyStableElementsNative DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPGroupCohomologyCentricLimit.
Section Limit.
Variable G : finGroupType.
Variable P : {group G}.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation S := [the finGroupType of [subg P]%type].
Local Notation F := (DPFiniteGroupFusion.system P).
Local Notation M := (native_cohomology_pair F A n).
Local Notation D := (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n).
Local Notation E := (@DPFusionStableLimit.centric_coefficient S F R M).

Definition pair_limit_to_native : module_hom (module_limit_type E) (module_limit_type D).
Proof.
exists (fun z : module_limit_type E => @submodule_in R (module_product_type (fobj D))
  (module_limit_subspace D) (module_limit_val z)
  (fun i j f => @module_limit_val_compatible R _ E z i j f)).
move=> r z w; apply module_limit_val_injective; reflexivity.
Defined.

Definition native_limit_to_pair : module_hom (module_limit_type D) (module_limit_type E).
Proof.
exists (fun z : module_limit_type D => @submodule_in R (module_product_type (fobj E))
  (module_limit_subspace E) (module_limit_val z)
  (fun i j f => @module_limit_val_compatible R _ D z i j f)).
move=> r z w; apply module_limit_val_injective; reflexivity.
Defined.

Definition native_limit_chart_iso : @isomorphism (module_category R)
    (module_limit_type E) (module_limit_type D).
Proof.
refine (@Build_isomorphism (module_category R) _ _ pair_limit_to_native native_limit_to_pair _ _);
apply module_hom_ext => z; apply module_limit_val_injective; reflexivity.
Defined.

Variable p : nat.
Variable hP : p.-Sylow([set: G]) P.
Variable u : R.
Variable hu : u * (indexg [set: G] P)%:R = 1.

Definition finite_group_centric_limit_iso : @isomorphism (module_category R)
    (value R G A n) (module_limit_type D) :=
  module_iso_comp (@finite_group_stable_iso G P R A n u hu)
    (module_iso_comp (iso_symm (@DPFusionStableLimit.stable_limit_iso S F R M p
      (DPFiniteGroupFusionSubgroups.sylow_carrier_pgroup hP)
      (DPFiniteGroupFusionSaturation.saturated hP))) native_limit_chart_iso).

Definition centric_ambient_inclusion (U : DPFusionOrbit.centric_object F) :
    {morphism [set: [subg (val U)]] >-> G} :=
  group_hom_comp (subgroup_inclusion_hom (val U)) (subgroup_inclusion_hom P).

Theorem finite_group_centric_limit_iso_component
    (U : DPFusionOrbit.centric_object F) z :
  module_limit_val (module_hom_fun (iso_hom finite_group_centric_limit_iso) z) U =
    module_hom_fun (pull A (centric_ambient_inclusion U) n) z.
Proof.
change (DPFusionStable.restrict_top M (val U)
  (submodule_val (module_hom_fun (iso_hom (@finite_group_stable_iso G P R A n u hu)) z)) =
  module_hom_fun (pull A (centric_ambient_inclusion U) n) z).
rewrite finite_group_stable_iso_value /top_ambient_inclusion pull_composition.
change (DPFusionStable.restrict_top M (val U)
  (module_hom_fun (pull A (subgroup_inclusion_hom [set: S]%G) n)
    (module_hom_fun (pull A (subgroup_inclusion_hom P) n) z)) =
  module_hom_fun (pull A (centric_ambient_inclusion U) n) z).
by rewrite top_restriction /centric_ambient_inclusion pull_composition.
Qed.

End Limit.
End DPGroupCohomologyCentricLimit.
