(** Literal subgroup charts used in the finite-group stable-elements theorem. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules FusionMaps FusionCentralizerMaps.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  GroupCohomologyHomogeneousComparison FiniteGroupFusionSubgroups.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyHomogeneousComparison DPFiniteGroupFusionSubgroups.
Local Open Scope group_scope.

Module DPGroupCohomologyStableElementsCharts.

Definition top_inverse_hom (G : finGroupType) :
    {morphism [set: G] >-> [subg [set: G]]} := [morphism of subg [set: G]].

Lemma top_inverse_hom_val (G : finGroupType) (x : G) :
  val (top_inverse_hom G x) = x.
Proof. apply: subgK; by rewrite inE. Qed.

Lemma top_forward_inverse (G : finGroupType) :
  group_hom_comp (subgroup_inclusion_hom [set: G]%G) (top_inverse_hom G) =
    group_hom_identity [the finGroupType of [subg [set: G]]%type].
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x.
change (subg [set: G] (val x) = x); exact: sgvalK.
Qed.

Lemma top_inverse_forward (G : finGroupType) :
  group_hom_comp (top_inverse_hom G) (subgroup_inclusion_hom [set: G]%G) =
    group_hom_identity G.
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x.
exact: top_inverse_hom_val.
Qed.

Definition top_cohomology_iso (R : comPzRingType) (G : finGroupType)
    (A : lmodType R) n : @isomorphism (module_category R)
    (value R G A n) (value R [the finGroupType of [subg [set: G]]%type] A n).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (pull A (subgroup_inclusion_hom [set: G]%G) n)
  (pull A (top_inverse_hom G) n) _ _).
- change (module_hom_comp (pull A (subgroup_inclusion_hom [set: G]%G) n)
    (pull A (top_inverse_hom G) n) = module_hom_id _).
  by rewrite -pull_composition top_inverse_forward pull_identity.
- change (module_hom_comp (pull A (top_inverse_hom G) n)
    (pull A (subgroup_inclusion_hom [set: G]%G) n) = module_hom_id _).
  by rewrite -pull_composition top_forward_inverse pull_identity.
Defined.

Section Ambient.
Variable G : finGroupType.
Variable P : {group G}.
Local Notation S := [the finGroupType of [subg P]%type].

Definition ambient_chart (U : {group S}) :
    {morphism [set: [subg U]] >-> [subg (DPFusionSubgroup.ambient U)]}.
Proof.
apply: (Morphism (mfun := fun x : [subg U] =>
  subg (DPFusionSubgroup.ambient U) (val (val x)))).
move=> x y _ _; apply val_inj.
rewrite subgM ?DPFusionSubgroup.ambient_mem ?subgP //.
Defined.

Lemma ambient_chart_val (U : {group S}) (x : [subg U]) :
  val (ambient_chart U x) = val (val x).
Proof. apply: subgK; exact: DPFusionSubgroup.ambient_mem (subgP x). Qed.

Definition ambient_inverse_chart (L : {group G}) (hLP : L \subset P) :
    {morphism [set: [subg L]] >-> [subg (from_ambient P L)]}.
Proof.
apply: (Morphism (mfun := fun x : [subg L] =>
  subg (from_ambient P L) (subg P (val x)))).
move=> x y _ _; rewrite subgM ?(subsetP hLP _ (subgP _)) //.
apply: subgM; apply: mem_morphim; first exact: subsetP hLP _ (subgP x).
- exact: subgP.
- exact: subsetP hLP _ (subgP y).
- exact: subgP.
Defined.

Lemma ambient_inverse_chart_val (L : {group G}) (hLP : L \subset P) (x : [subg L]) :
  val (ambient_inverse_chart hLP x) = subg P (val x).
Proof.
apply: subgK; apply: mem_morphim; [exact: subsetP hLP _ (subgP x)|exact: subgP].
Qed.

End Ambient.
End DPGroupCohomologyStableElementsCharts.
