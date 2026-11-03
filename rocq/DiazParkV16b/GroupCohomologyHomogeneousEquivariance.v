(** Equivariance of the literal deletion differential and augmentation. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category BarPaths BarFreeModule BarResolutionTerms.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyHomogeneousPaths
  GroupCohomologyHomogeneousFaces GroupCohomologyHomogeneousComplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyHomogeneousPaths
  DPGroupCohomologyHomogeneousFaces DPGroupCohomologyHomogeneousComplex
  DiazParkBarPaths DiazParkFreeModule DiazParkBarResolutionTerms.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousEquivariance.
Section Equivariance.
Variable R : pzRingType.
Variable G : finGroupType.

Definition homogeneous_action n (a : G) :
    {linear homogeneous_term R G n -> homogeneous_term R G n} :=
  free_map R (@left_translate G n.+1 a).

Lemma homogeneous_action_basis n (a : G) (v : homogeneous_generator G n) :
  homogeneous_action n a (free_basis R v) = free_basis R (left_translate n.+1 a v).
Proof. exact: free_map_basis. Qed.

Lemma homogeneous_action_identity n (v : homogeneous_term R G n) :
  homogeneous_action n 1%g v = v.
Proof.
rewrite /homogeneous_action.
have h : @left_translate G n.+1 1%g = idfun.
  apply functional_extensionality_dep => x; exact: left_translate_identity.
by rewrite h free_map_identity.
Qed.

Lemma homogeneous_action_composition n (a b : G) (v : homogeneous_term R G n) :
  homogeneous_action n (a * b)%g v = homogeneous_action n a (homogeneous_action n b v).
Proof.
rewrite /homogeneous_action -free_map_composition.
congr (free_map R _ v); apply functional_extensionality_dep => x.
exact: left_translate_composition.
Qed.

Lemma homogeneous_action_boundary n (a : G) (v : homogeneous_term R G n.+1) :
  homogeneous_boundary R G n (homogeneous_action n.+1 a v) =
    homogeneous_action n a (homogeneous_boundary R G n v).
Proof.
rewrite !homogeneous_boundary_formula linear_sum.
apply: eq_bigr => i _; rewrite linearZ; congr (_ *: _).
rewrite /homogeneous_action -!free_map_composition.
congr (free_map R _ v); apply functional_extensionality_dep => x.
exact: delete_vertex_translate.
Qed.

Lemma homogeneous_action_augmentation (a : G) (v : homogeneous_term R G 0) :
  homogeneous_augmentation R G (homogeneous_action 0 a v) =
    homogeneous_augmentation R G v.
Proof.
apply: (free_lift_ext
  (g := (homogeneous_augmentation R G \o homogeneous_action 0 a :
    {linear homogeneous_term R G 0 -> R^o}))
  (h := homogeneous_augmentation R G)).
move=> x.
change (homogeneous_augmentation R G (homogeneous_action 0 a (free_basis R x)) =
  homogeneous_augmentation R G (free_basis R x)).
rewrite homogeneous_action_basis !homogeneous_augmentation_basis.
reflexivity.
Qed.

Lemma to_homogeneous_action n (a : G) (v : ambient_bar_term R G n) :
  to_homogeneous R G n (free_map R (@path_precompose (group_category G) n tt tt a) v) =
    homogeneous_action n a (to_homogeneous R G n v).
Proof.
rewrite /to_homogeneous /homogeneous_action -!free_map_composition.
congr (free_map R _ v); apply functional_extensionality_dep => x.
exact: homogeneous_precompose.
Qed.

End Equivariance.
End DPGroupCohomologyHomogeneousEquivariance.
