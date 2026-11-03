(** Fusion stability implies the literal native conjugation equalities. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules FusionMaps FusionSystems
  FusionOrbit FusionMackeyShape FusionCentralizerMaps FusionStableElements.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyHomogeneousComparison
  GroupCohomologyHomogeneousRestriction GroupCohomologyHomogeneousConjugation
  GroupCohomologyOrbitCoefficient GroupCohomologyMackeyPair
  LinkingCommaNaturality FiniteGroupFusion FiniteGroupFusionSubgroups
  GroupCohomologyStableElementsBase GroupCohomologyStableElementsCharts
  GroupCohomologyStableElementsFusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyHomogeneousComparison DPGroupCohomologyHomogeneousRestriction
  DPGroupCohomologyHomogeneousConjugation DPGroupCohomologyMackeyPair
  DPLinkingCommaNaturality DPFiniteGroupFusionSubgroups
  DPGroupCohomologyStableElementsBase DPGroupCohomologyStableElementsCharts
  DPGroupCohomologyStableElementsFusion.
Local Open Scope group_scope.

Module DPGroupCohomologyStableElementsFusionInverse.
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

Lemma from_conjugate_sub (L : {group G}) (hLP : L \subset P)
    (x : G) (hLx : L \subset P :^ x) :
  (DPFusionSubgroup.ambient (from_ambient P L)) :^ x^-1 \subset
    DPFusionSubgroup.ambient topS.
Proof. by rewrite ambient_from // ambient_top sub_conjg invgK. Qed.

Definition from_conjugation_arrow (L : {group G}) (hLP : L \subset P)
    (x : G) (hLx : L \subset P :^ x) :
    DPFusionSystem.arrow F (from_ambient P L) topS :=
  Sub (DPFiniteGroupFusion.conjugation_map (from_conjugate_sub hLP hLx))
    (DPFiniteGroupFusion.conjugation_map_allowed (from_conjugate_sub hLP hLx)).

Lemma from_chart_inclusion (L : {group G}) (hLP : L \subset P) :
  group_hom_comp (ambient_inverse_chart hLP)
    (subgroup_inclusion_hom (from_ambient P L)) = subgroup_nested_hom hLP.
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => a; apply val_inj.
change (val (val (ambient_inverse_chart hLP a)) = val (subgroup_nested_hom hLP a)).
by rewrite ambient_inverse_chart_val subgroup_nested_hom_val.
Qed.

Lemma from_chart_conjugation (L : {group G}) (hLP : L \subset P)
    (x : G) (hLx : L \subset P :^ x) :
  group_hom_comp (ambient_inverse_chart hLP)
    (group_hom_comp (arrow_group_hom (from_conjugation_arrow hLP hLx))
      (subgroup_inclusion_hom topS)) =
    @subgroup_conjugation_hom G L P x hLx.
Proof.
apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext => a; apply val_inj.
change (val (DPFiniteGroupFusion.conjugation_map (from_conjugate_sub hLP hLx)
    (val (ambient_inverse_chart hLP a))) = val (subgroup_conjugation_hom hLx a)).
rewrite DPFiniteGroupFusion.conjugation_mapE ?subgP //
  subgroup_conjugation_hom_val ambient_inverse_chart_val subgK //.
exact: subsetP hLP _ (subgP a).
Qed.

Theorem fusion_stable_native (z : value R S A n)
    (hz : @DPFusionStable.stable_element S F R M
      (module_hom_fun (pull A (subgroup_inclusion_hom topS) n) z)) :
    @stable R G P topG A n z.
Proof.
move=> L hLP x hx hLx.
have hs := @DPFusionStable.stable_all_arrows S F R M _ hz
  (from_ambient P L) topS (from_conjugation_arrow hLP hLx).
rewrite !top_restriction /DPFusionStable.raw_pull native_pair_pull_class in hs.
change (module_hom_fun (pull A (arrow_group_hom (from_conjugation_arrow hLP hLx)) n)
    (module_hom_fun (pull A (subgroup_inclusion_hom topS) n) z) =
  module_hom_fun (pull A (subgroup_inclusion_hom (from_ambient P L)) n) z) in hs.
have hs' := congr1 (fun q => module_hom_fun (pull A (ambient_inverse_chart hLP) n) q) hs.
have hc := congr1 (fun f => module_hom_fun f z)
  (@pull_composition R A _ _ _ (arrow_group_hom (from_conjugation_arrow hLP hLx))
    (subgroup_inclusion_hom topS) n).
change (module_hom_fun (pull A (group_hom_comp
  (arrow_group_hom (from_conjugation_arrow hLP hLx)) (subgroup_inclusion_hom topS)) n) z =
  module_hom_fun (pull A (arrow_group_hom (from_conjugation_arrow hLP hLx)) n)
    (module_hom_fun (pull A (subgroup_inclusion_hom topS) n) z)) in hc.
rewrite -hc in hs'.
change (module_hom_fun (module_hom_comp (pull A (group_hom_comp
  (arrow_group_hom (from_conjugation_arrow hLP hLx)) (subgroup_inclusion_hom topS)) n)
  (pull A (ambient_inverse_chart hLP) n)) z =
  module_hom_fun (module_hom_comp (pull A (subgroup_inclusion_hom (from_ambient P L)) n)
  (pull A (ambient_inverse_chart hLP) n)) z) in hs'.
by rewrite -!pull_composition from_chart_conjugation from_chart_inclusion in hs'.
Qed.

End Fusion.
End DPGroupCohomologyStableElementsFusionInverse.
