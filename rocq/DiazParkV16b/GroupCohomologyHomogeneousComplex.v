(** The actual free homogeneous group complex, with its deletion formula
    and an explicit contraction.  Its terms are free on G^(n+1). *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules BarPaths BarFreeModule
  BarResolutionTerms BarResolutionFaces BarResolutionDifferential
  BarResolutionAugmentation BarResolutionContraction.
From DiazParkV16b Require Import ChainComplex GroupCohomologyBase
  GroupCohomologyHomogeneousPaths GroupCohomologyHomogeneousFaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPChainComplex
  DPGroupCohomologyHomogeneousPaths DPGroupCohomologyHomogeneousFaces
  DiazParkBarPaths DiazParkFreeModule DiazParkBarResolutionTerms
  DiazParkBarResolutionFaces DiazParkBarResolutionDifferential
  DiazParkBarResolutionAugmentation DiazParkBarResolutionContraction.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousComplex.
Section Homogeneous.
Variable R : pzRingType.
Variable G : finGroupType.

Definition homogeneous_term n : lmodType R := free_module R (homogeneous_generator G n).
Definition ambient_bar_term n : lmodType R :=
  @resolution_term_obj R (group_category G) n tt.

Definition to_homogeneous n : {linear ambient_bar_term n -> homogeneous_term n} :=
  free_map R (@resolution_generator_to_homogeneous G n tt).

Definition from_homogeneous n : {linear homogeneous_term n -> ambient_bar_term n} :=
  free_map R (@homogeneous_to_resolution_generator G n tt).

Lemma to_from_homogeneous n (a : homogeneous_term n) :
  to_homogeneous n (from_homogeneous n a) = a.
Proof.
rewrite /to_homogeneous /from_homogeneous -free_map_composition.
have h : @resolution_generator_to_homogeneous G n tt \o
    @homogeneous_to_resolution_generator G n tt = idfun.
  apply functional_extensionality_dep => v; exact: homogeneous_generator_inverse.
by rewrite h free_map_identity.
Qed.

Lemma from_to_homogeneous n (a : ambient_bar_term n) :
  from_homogeneous n (to_homogeneous n a) = a.
Proof.
rewrite /to_homogeneous /from_homogeneous -free_map_composition.
have h : @homogeneous_to_resolution_generator G n tt \o
    @resolution_generator_to_homogeneous G n tt = idfun.
  apply functional_extensionality_dep => v; exact: resolution_generator_inverse.
by rewrite h free_map_identity.
Qed.

Lemma to_homogeneous_face n i (a : ambient_bar_term n.+1) :
  to_homogeneous n (@resolution_face_linear R (group_category G) n i tt a) =
    free_map R (@delete_vertex G n.+1 i) (to_homogeneous n.+1 a).
Proof.
apply: (free_lift_ext
  (g := (to_homogeneous n \o @resolution_face_linear R (group_category G) n i tt :
    {linear ambient_bar_term n.+1 -> homogeneous_term n}))
  (h := (free_map R (@delete_vertex G n.+1 i) \o to_homogeneous n.+1 :
    {linear ambient_bar_term n.+1 -> homogeneous_term n}))).
move=> p.
change (free_map R (@resolution_generator_to_homogeneous G n tt)
    (free_map R (@path_inner_face (group_category G) n.+1 i tt) (free_basis R p)) =
  free_map R (@delete_vertex G n.+1 i)
    (free_map R (@resolution_generator_to_homogeneous G n.+1 tt) (free_basis R p))).
by rewrite !free_map_basis homogeneous_face.
Qed.

Lemma to_homogeneous_boundary n (a : ambient_bar_term n.+1) :
  to_homogeneous n (@resolution_boundary_fun R (group_category G) n tt a) =
    \sum_(i < n.+2) (-1) ^+ i *:
      free_map R (@delete_vertex G n.+1 i) (to_homogeneous n.+1 a).
Proof.
rewrite /resolution_boundary_fun linear_sum.
apply: eq_bigr => i _; by rewrite linearZ to_homogeneous_face.
Qed.

Definition homogeneous_boundary n :
    {linear homogeneous_term n.+1 -> homogeneous_term n} :=
  (to_homogeneous n \o @resolution_boundary_fun R (group_category G) n tt \o
    from_homogeneous n.+1 : {linear homogeneous_term n.+1 -> homogeneous_term n}).

Lemma homogeneous_boundary_formula n (a : homogeneous_term n.+1) :
  homogeneous_boundary n a = \sum_(i < n.+2) (-1) ^+ i *:
    free_map R (@delete_vertex G n.+1 i) a.
Proof.
rewrite /homogeneous_boundary /= to_homogeneous_boundary to_from_homogeneous.
reflexivity.
Qed.

Lemma homogeneous_boundary_squared n (a : homogeneous_term n.+2) :
  homogeneous_boundary n (homogeneous_boundary n.+1 a) = 0.
Proof.
rewrite /homogeneous_boundary /= from_to_homogeneous
  resolution_boundary_squared linear0; reflexivity.
Qed.

Definition homogeneous_complex : @chain_complex R :=
  @ChainComplex R homogeneous_term homogeneous_boundary homogeneous_boundary_squared.

Definition homogeneous_augmentation : {linear homogeneous_term 0 -> R^o} :=
  (@resolution_augmentation_fun R (group_category G) tt \o from_homogeneous 0 :
    {linear homogeneous_term 0 -> R^o}).

Lemma homogeneous_augmentation_basis (v : homogeneous_generator G 0) :
  homogeneous_augmentation (free_basis R v) = 1.
Proof.
rewrite /homogeneous_augmentation /= /from_homogeneous free_map_basis.
exact (@resolution_augmentation_basis R (group_category G) tt
  (@homogeneous_to_resolution_generator G 0 tt v)).
Qed.

Lemma homogeneous_augmentation_boundary (a : homogeneous_term 1) :
  homogeneous_augmentation (homogeneous_boundary 0 a) = 0.
Proof.
rewrite /homogeneous_augmentation /homogeneous_boundary /= from_to_homogeneous.
exact (@resolution_augmentation_boundary R (group_category G) tt (from_homogeneous 1 a)).
Qed.

Definition homogeneous_section : {linear R^o -> homogeneous_term 0} :=
  (to_homogeneous 0 \o @resolution_augmentation_section_fun R (group_category G) tt :
    {linear R^o -> homogeneous_term 0}).

Lemma homogeneous_augmentation_section (r : R^o) :
  homogeneous_augmentation (homogeneous_section r) = r.
Proof.
rewrite /homogeneous_augmentation /homogeneous_section /= from_to_homogeneous.
exact (@resolution_augmentation_section R (group_category G) tt r).
Qed.

Definition homogeneous_contraction n :
    {linear homogeneous_term n -> homogeneous_term n.+1} :=
  (to_homogeneous n.+1 \o @resolution_contraction R (group_category G) n tt \o
    from_homogeneous n : {linear homogeneous_term n -> homogeneous_term n.+1}).

Lemma homogeneous_contraction_basis n (v : homogeneous_generator G n) :
  homogeneous_contraction n (free_basis R v) = free_basis R (insert_vertex n.+1 v).
Proof.
change (to_homogeneous n.+1 (@resolution_contraction R (group_category G) n tt
  (from_homogeneous n (free_basis R v))) = free_basis R (insert_vertex n.+1 v)).
rewrite /from_homogeneous free_map_basis
  resolution_contraction_basis /to_homogeneous free_map_basis homogeneous_insert.
by rewrite homogeneous_generator_inverse.
Qed.

Lemma homogeneous_contraction_zero (a : homogeneous_term 0) :
  homogeneous_boundary 0 (homogeneous_contraction 0 a) +
    homogeneous_section (homogeneous_augmentation a) = a.
Proof.
rewrite /homogeneous_boundary /homogeneous_contraction
  /homogeneous_section /homogeneous_augmentation /= from_to_homogeneous.
have h := congr1 (to_homogeneous 0)
  (@resolution_contraction_zero R (group_category G) tt (from_homogeneous 0 a)).
rewrite linearD to_from_homogeneous in h; exact h.
Qed.

Lemma homogeneous_contraction_successor n (a : homogeneous_term n.+1) :
  homogeneous_boundary n.+1 (homogeneous_contraction n.+1 a) +
    homogeneous_contraction n (homogeneous_boundary n a) = a.
Proof.
rewrite /homogeneous_boundary /homogeneous_contraction /= !from_to_homogeneous.
have h := congr1 (to_homogeneous n.+1)
  (@resolution_contraction_successor R (group_category G) n tt (from_homogeneous n.+1 a)).
rewrite linearD to_from_homogeneous in h; exact h.
Qed.

Lemma homogeneous_exact_zero (a : homogeneous_term 0) :
  homogeneous_augmentation a = 0 -> exists b, homogeneous_boundary 0 b = a.
Proof.
move=> ha; exists (homogeneous_contraction 0 a).
have h := homogeneous_contraction_zero a.
by rewrite ha linear0 addr0 in h.
Qed.

Lemma homogeneous_exact_successor n (a : homogeneous_term n.+1) :
  homogeneous_boundary n a = 0 -> exists b, homogeneous_boundary n.+1 b = a.
Proof.
move=> ha; exists (homogeneous_contraction n.+1 a).
have h := homogeneous_contraction_successor a.
by rewrite ha linear0 addr0 in h.
Qed.

End Homogeneous.
End DPGroupCohomologyHomogeneousComplex.
