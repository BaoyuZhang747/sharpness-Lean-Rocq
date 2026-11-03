(** A normalized comparison from each subgroup's actual bar resolution
    to the common ambient homogeneous resolution. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryDiagramHomLimit CategoryEnoughProjectivesResolution CategoryEnoughProjectivesComparison
  BarPaths BarFreeModule BarResolutionTerms BarResolutionDifferential BarResolutionAugmentation
  ProjectiveExtBar.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyHomogeneousPaths GroupCohomologyHomogeneousComplex
  GroupCohomologyHomogeneousEquivariance GroupCohomologyHomogeneousMaps
  GroupCohomologyHomogeneousProjective GroupCohomologyHomogeneousResolution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyFunctor
  DPEnoughProjectiveResolutions DPProjectiveComparison DPProjectiveExtBar
  DiazParkBarPaths DiazParkFreeModule DiazParkBarResolutionTerms
  DiazParkBarResolutionDifferential DiazParkBarResolutionAugmentation
  DPGroupCohomologyHomogeneousPaths DPGroupCohomologyHomogeneousComplex
  DPGroupCohomologyHomogeneousEquivariance DPGroupCohomologyHomogeneousMaps
  DPGroupCohomologyHomogeneousProjective DPGroupCohomologyHomogeneousResolution.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousComparison.

Definition subgroup_inclusion_hom (G : finGroupType) (H : {group G}) :
    {morphism [set: [subg H]] >-> G} := [morphism of @sgval G H].

Lemma homogeneous_map_action (R : pzRingType) (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) n a (v : homogeneous_term R G n) :
  homogeneous_map R f n (homogeneous_action R n a v) =
    homogeneous_action R n (f a) (homogeneous_map R f n v).
Proof.
rewrite /homogeneous_map /homogeneous_action -!free_map_composition.
congr (free_map R _ v); apply functional_extensionality_dep => x.
exact: vertices_map_translate.
Qed.

Lemma homogeneous_boundary_to_homogeneous (R : pzRingType) (G : finGroupType)
    n (v : ambient_bar_term R G n.+1) :
  homogeneous_boundary R G n (to_homogeneous R G n.+1 v) =
    to_homogeneous R G n (@resolution_boundary_fun R (group_category G) n tt v).
Proof. by rewrite /homogeneous_boundary /= from_to_homogeneous. Qed.

Section Comparison.
Variable R : comPzRingType.
Variable G : finGroupType.
Variable H : {group G}.
Local Notation HS := [the finGroupType of [subg H]].
Local Notation C := (opposite (group_category HS)).

Definition native_to_ambient_component n :
    {linear ambient_bar_term R HS n -> homogeneous_term R G n} :=
  (homogeneous_map R (subgroup_inclusion_hom H) n \o to_homogeneous R HS n :
    {linear ambient_bar_term R HS n -> homogeneous_term R G n}).

Definition native_to_ambient_term n :
    nat_trans (@resolution_term R (group_category HS) n) (homogeneous_diagram R H n).
Proof.
refine (@Build_nat_trans C (module_category R)
  (@resolution_term R (group_category HS) n) (homogeneous_diagram R H n)
  (fun _ => module_hom_of_linear (native_to_ambient_component n)) _).
move=> x y a; apply module_hom_ext => v.
change (homogeneous_map R (subgroup_inclusion_hom H) n
    (to_homogeneous R HS n (free_map R (@path_precompose (group_category HS) n tt tt a) v)) =
  homogeneous_action R n (val a)
    (homogeneous_map R (subgroup_inclusion_hom H) n (to_homogeneous R HS n v))).
rewrite to_homogeneous_action homogeneous_map_action; reflexivity.
Defined.

Lemma native_to_ambient_boundary n (v : ambient_bar_term R HS n.+1) :
  homogeneous_boundary R G n (native_to_ambient_component n.+1 v) =
    native_to_ambient_component n (@resolution_boundary_fun R (group_category HS) n tt v).
Proof.
change (homogeneous_boundary R G n
    (homogeneous_map R (subgroup_inclusion_hom H) n.+1 (to_homogeneous R HS n.+1 v)) =
  homogeneous_map R (subgroup_inclusion_hom H) n
    (to_homogeneous R HS n (@resolution_boundary_fun R (group_category HS) n tt v))).
by rewrite homogeneous_map_boundary homogeneous_boundary_to_homogeneous.
Qed.

Lemma native_to_ambient_augmentation (v : ambient_bar_term R HS 0) :
  homogeneous_augmentation R G (native_to_ambient_component 0 v) =
    @resolution_augmentation_fun R (group_category HS) tt v.
Proof.
change (homogeneous_augmentation R G
  (homogeneous_map R (subgroup_inclusion_hom H) 0 (to_homogeneous R HS 0 v)) =
  @resolution_augmentation_fun R (group_category HS) tt v).
by rewrite homogeneous_map_augmentation /homogeneous_augmentation /= from_to_homogeneous.
Qed.

Definition native_to_ambient_resolution :
    projective_resolution_map (@bar_projective_resolution R (group_category HS))
      (homogeneous_resolution R H) (nat_id (constant_regular_diagram R C)).
Proof.
refine (@Build_projective_resolution_map R C _ _
  (@bar_projective_resolution R (group_category HS)) (homogeneous_resolution R H)
  (nat_id (constant_regular_diagram R C)) native_to_ambient_term _ _).
- move=> n x v; exact: native_to_ambient_boundary.
- apply nat_trans_ext => x; apply module_hom_ext => v.
  exact: native_to_ambient_augmentation.
Defined.

Lemma native_to_ambient_basis n (p : @path_from (group_category HS) n.+1 tt) :
  native_to_ambient_component n (free_basis R p) =
    free_basis R (vertices_map (subgroup_inclusion_hom H) n.+1
      (@resolution_generator_to_homogeneous HS n tt p)).
Proof.
change (free_map R (@vertices_map HS G (subgroup_inclusion_hom H) n.+1)
  (free_map R (@resolution_generator_to_homogeneous HS n tt) (free_basis R p)) =
  free_basis R (vertices_map (subgroup_inclusion_hom H) n.+1
    (@resolution_generator_to_homogeneous HS n tt p))).
by rewrite !free_map_basis.
Qed.

End Comparison.
End DPGroupCohomologyHomogeneousComparison.
