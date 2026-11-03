(** Cartan--Eilenberg stable elements for the actual native cohomology,
    with literal restriction as the forward map and arbitrary coefficients. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers HomologicalModuleIso
  FusionStableElements FusionStableLimit.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyHomogeneousComparison
  GroupCohomologyHomogeneousRestriction GroupCohomologyOrbitCoefficient
  GroupCohomologyMackeyPair FiniteGroupFusion
  GroupCohomologyStableElementsBase GroupCohomologyStableElementsIso
  GroupCohomologyStableElementsCharts GroupCohomologyStableElementsFusion
  GroupCohomologyStableElementsFusionInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyFunctor
  DPGroupCohomologyPullback DPGroupCohomologyHomogeneousComparison
  DPGroupCohomologyHomogeneousRestriction DPGroupCohomologyMackeyPair
  DPGroupCohomologyStableElementsCharts DPGroupCohomologyStableElementsFusion
  DPGroupCohomologyStableElementsFusionInverse DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPGroupCohomologyStableElementsNative.
Section Native.
Variable G : finGroupType.
Variable P : {group G}.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation S := [the finGroupType of [subg P]].
Local Notation F := (DPFiniteGroupFusion.system P).
Local Notation M := (native_cohomology_pair F A n).
Local Notation topS := [set: S]%G.
Local Notation topG := [set: G]%G.
Local Notation NativeStable := (@DPGroupCohomologyStableElementsIso.stable_module R G P topG A n).
Local Notation FusionStable := (@DPFusionStableLimit.stable_module S F R M).
Local Notation E := (top_cohomology_iso S A n).

Definition native_to_fusion_stable : module_hom NativeStable FusionStable.
Proof.
exists (fun z : NativeStable => @submodule_in R _ (@DPFusionStableLimit.stable_subspace S F R M)
  (module_hom_fun (iso_hom E) (submodule_val z))
  (@native_stable_fusion G P R A n _ (submodule_val_mem z))).
move=> r z w; apply submodule_val_injective.
change (module_hom_fun (iso_hom E)
  (submodule_val (r *: z + w)) =
  r *: module_hom_fun (iso_hom E) (submodule_val z) +
    module_hom_fun (iso_hom E) (submodule_val w)).
by rewrite submodule_val_linear module_hom_linear.
Defined.

Lemma inverse_top_stable (z : FusionStable) :
  @DPGroupCohomologyStableElementsBase.stable R G P topG A n
    (module_hom_fun (iso_inv E) (submodule_val z)).
Proof.
apply fusion_stable_native.
change (@DPFusionStable.stable_element S F R M
  (module_hom_fun (iso_hom E) (module_hom_fun (iso_inv E) (submodule_val z)))).
rewrite module_iso_inv_hom_apply; exact (submodule_val_mem z).
Qed.

Definition fusion_to_native_stable : module_hom FusionStable NativeStable.
Proof.
exists (fun z : FusionStable => @submodule_in R _
  (@DPGroupCohomologyStableElementsIso.stable_subspace R G P topG A n)
  (module_hom_fun (iso_inv E) (submodule_val z)) (inverse_top_stable z)).
move=> r z w; apply submodule_val_injective.
change (module_hom_fun (iso_inv E)
  (submodule_val (r *: z + w)) =
  r *: module_hom_fun (iso_inv E) (submodule_val z) +
    module_hom_fun (iso_inv E) (submodule_val w)).
by rewrite submodule_val_linear module_hom_linear.
Defined.

Definition stable_chart_iso : @isomorphism (module_category R) NativeStable FusionStable.
Proof.
refine (@Build_isomorphism (module_category R) _ _ native_to_fusion_stable fusion_to_native_stable _ _).
- apply module_hom_ext => z; apply submodule_val_injective.
  exact: module_iso_hom_inv_apply E (submodule_val z).
- apply module_hom_ext => z; apply submodule_val_injective.
  exact: module_iso_inv_hom_apply E (submodule_val z).
Defined.

Variable u : R.
Hypothesis hu : u * (indexg topG P)%:R = 1.

Definition finite_group_stable_iso : @isomorphism (module_category R)
    (value R G A n) FusionStable :=
  module_iso_comp (top_cohomology_iso G A n)
    (module_iso_comp
      (@DPGroupCohomologyStableElementsIso.restriction_stable_iso R G P topG
        (subsetT P) A n u hu) stable_chart_iso).

Definition top_ambient_inclusion :
    {morphism [set: [subg topS]] >-> G} :=
  group_hom_comp (subgroup_inclusion_hom topS) (subgroup_inclusion_hom P).

Theorem finite_group_stable_iso_value z :
  submodule_val (module_hom_fun (iso_hom finite_group_stable_iso) z) =
    module_hom_fun (pull A top_ambient_inclusion n) z.
Proof.
change (module_hom_fun (pull A (subgroup_inclusion_hom topS) n)
  (module_hom_fun (pull A (subgroup_nested_hom (subsetT P)) n)
    (module_hom_fun (pull A (subgroup_inclusion_hom topG) n) z)) =
  module_hom_fun (pull A top_ambient_inclusion n) z).
have e : group_hom_comp (subgroup_nested_hom (subsetT P))
    (subgroup_inclusion_hom topG) = subgroup_inclusion_hom P.
  apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => a.
  exact: subgroup_nested_hom_val.
have hc := congr1 (fun f => module_hom_fun f z)
  (@pull_composition R A _ _ _ (subgroup_nested_hom (subsetT P))
    (subgroup_inclusion_hom topG) n).
change (module_hom_fun (pull A (group_hom_comp (subgroup_nested_hom (subsetT P))
  (subgroup_inclusion_hom topG)) n) z =
  module_hom_fun (pull A (subgroup_nested_hom (subsetT P)) n)
    (module_hom_fun (pull A (subgroup_inclusion_hom topG) n) z)) in hc.
rewrite -hc e /top_ambient_inclusion pull_composition; reflexivity.
Qed.

End Native.
End DPGroupCohomologyStableElementsNative.
