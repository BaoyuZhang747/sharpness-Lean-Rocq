(** Comparison of the native conjugation stability predicate with the
    actual induced fusion-system stable-elements predicate. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules FusionMaps FusionSystems
  FusionOrbit FusionMackeyShape FusionCentralizerMaps FusionStableElements.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyHomogeneousComparison
  GroupCohomologyHomogeneousRestriction GroupCohomologyHomogeneousConjugation
  GroupCohomologyOrbitCoefficient GroupCohomologyMackeyPushBase GroupCohomologyMackeyPair
  LinkingCommaNaturality FiniteGroupFusion FiniteGroupFusionSubgroups
  GroupCohomologyStableElementsBase GroupCohomologyStableElementsCharts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyHomogeneousComparison DPGroupCohomologyHomogeneousRestriction
  DPGroupCohomologyHomogeneousConjugation DPGroupCohomologyMackeyPushBase
  DPGroupCohomologyMackeyPair DPLinkingCommaNaturality
  DPGroupCohomologyStableElementsBase DPGroupCohomologyStableElementsCharts.
Local Open Scope group_scope.

Module DPGroupCohomologyStableElementsFusion.
Section Fusion.
Variable G : finGroupType.
Variable P : {group G}.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation S := [the finGroupType of [subg P]%type].
Local Notation F := (DPFiniteGroupFusion.system P).
Local Notation M := (native_cohomology_pair F A n).
Local Notation topS := [set: S]%G.
Local Notation topG := [set: G]%G.

Lemma top_restriction (U : {group S}) (z : value R S A n) :
  DPFusionStable.restrict_top M U
    (module_hom_fun (pull A (subgroup_inclusion_hom topS) n) z) =
  module_hom_fun (pull A (subgroup_inclusion_hom U) n) z.
Proof.
rewrite /DPFusionStable.restrict_top /DPFusionStable.raw_pull native_pair_pull_class
  /DPFusionStable.inclusion raw_pull_inclusion.
have e : group_hom_comp (subgroup_nested_hom (subsetT U))
    (subgroup_inclusion_hom topS) = subgroup_inclusion_hom U.
  apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x.
  exact: subgroup_nested_hom_val.
have hc := congr1 (fun f => module_hom_fun f z)
  (@pull_composition R A _ _ _ (subgroup_nested_hom (subsetT U))
    (subgroup_inclusion_hom topS) n).
rewrite e in hc; exact: esym hc.
Qed.

Lemma ambient_chart_inclusion (U : {group S}) :
  group_hom_comp (ambient_chart U)
    (subgroup_nested_hom (DPFusionSubgroup.ambient_sub U)) =
    subgroup_inclusion_hom U.
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x; apply val_inj.
change (val (subgroup_nested_hom (DPFusionSubgroup.ambient_sub U) (ambient_chart U x)) =
  val (val x)).
by rewrite subgroup_nested_hom_val ambient_chart_val.
Qed.

Lemma allowed_stable_sub (U V : {group S}) (a : DPFusionSystem.arrow F U V)
    (g : G) (hg : {in U, forall x, val (val a x) = (val x)^g}) :
  DPFusionSubgroup.ambient U \subset (P :^ g^-1).
Proof.
apply/subsetP=> y /morphimP[x _ hx ->].
rewrite mem_conjg invgK -(hg x hx); exact: subgP.
Qed.

Lemma ambient_chart_conjugation (U V : {group S}) (a : DPFusionSystem.arrow F U V)
    (g : G) (hg : {in U, forall x, val (val a x) = (val x)^g}) :
  group_hom_comp (ambient_chart U)
    (@subgroup_conjugation_hom G (DPFusionSubgroup.ambient U) P g^-1
      (allowed_stable_sub hg)) =
  group_hom_comp (arrow_group_hom a) (subgroup_inclusion_hom V).
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => x; apply val_inj.
change (val (@subgroup_conjugation_hom G (DPFusionSubgroup.ambient U) P g^-1
    (allowed_stable_sub hg) (ambient_chart U x)) = val (val a (val x))).
by rewrite subgroup_conjugation_hom_val invgK ambient_chart_val hg ?subgP.
Qed.

Theorem native_stable_fusion (z : value R S A n)
    (hz : @stable R G P topG A n z) :
  @DPFusionStable.stable_element S F R M
    (module_hom_fun (pull A (subgroup_inclusion_hom topS) n) z).
Proof.
move=> U V a ha.
rewrite !top_restriction /DPFusionStable.raw_pull native_pair_pull_class.
change (module_hom_fun (pull A (arrow_group_hom a) n)
    (module_hom_fun (pull A (subgroup_inclusion_hom V) n) z) =
  module_hom_fun (pull A (subgroup_inclusion_hom U) n) z).
have /DPFiniteGroupFusion.allowedP[g hg] := valP a.
have hx : g^-1 \in topG by rewrite inE.
have hc := hz (DPFusionSubgroup.ambient U) (DPFusionSubgroup.ambient_sub U)
  g^-1 hx (allowed_stable_sub hg).
have hp := congr1 (fun q => module_hom_fun (pull A (ambient_chart U) n) q) hc.
change (module_hom_fun (module_hom_comp
  (pull A (@subgroup_conjugation_hom G (DPFusionSubgroup.ambient U) P g^-1
    (allowed_stable_sub hg)) n) (pull A (ambient_chart U) n)) z =
  module_hom_fun (module_hom_comp (pull A
    (subgroup_nested_hom (DPFusionSubgroup.ambient_sub U)) n)
    (pull A (ambient_chart U) n)) z) in hp.
rewrite -!pull_composition ambient_chart_conjugation ambient_chart_inclusion in hp.
by rewrite pull_composition in hp.
Qed.

End Fusion.
End DPGroupCohomologyStableElementsFusion.
