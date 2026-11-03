(** Actual vertexwise maps of the homogeneous complexes and their normalized
    comparison with the one-object functor maps on native bar generators. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category BarPaths BarFreeModule.
From DiazParkV16b Require Import ChainComplex GroupCohomologyBase GroupCohomologyFunctor
  CategoryBarPullbackPaths GroupCohomologyHomogeneousPaths
  GroupCohomologyHomogeneousFaces GroupCohomologyHomogeneousComplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPGroupCohomology DPGroupCohomologyFunctor
  DPCategoryBarPullback DPGroupCohomologyHomogeneousPaths
  DPGroupCohomologyHomogeneousFaces DPGroupCohomologyHomogeneousComplex
  DiazParkBarPaths DiazParkFreeModule.
Local Open Scope ring_scope.

Module DPGroupCohomologyHomogeneousMaps.

Fixpoint vertices_map (G H : finGroupType) (f : G -> H) (n : nat) :
    power G n -> power H n :=
  match n return power G n -> power H n with
  | 0 => fun _ => tt
  | k.+1 => fun v => (f v.1, @vertices_map G H f k v.2)
  end.

Arguments vertices_map {G H} f n _.

Lemma vertices_map_delete (G H : finGroupType) (f : G -> H) n i (v : power G n.+1) :
  delete_vertex n i (vertices_map f n.+1 v) = vertices_map f n (delete_vertex n i v).
Proof.
elim: n i v => [|n IH] i v; first reflexivity.
case: v => a v; case: i => [|i]; first reflexivity.
by rewrite /= IH.
Qed.

Lemma vertices_map_identity (G : finGroupType) n (v : power G n) :
  vertices_map idfun n v = v.
Proof.
elim: n v => [|n IH] v; first by case: v.
by case: v => a v; rewrite /= IH.
Qed.

Lemma vertices_map_composition (G H K : finGroupType) (f : G -> H) (g : H -> K)
    n (v : power G n) :
  vertices_map (g \o f) n v = vertices_map g n (vertices_map f n v).
Proof.
elim: n v => [|n IH] v; first reflexivity.
by case: v => a v; rewrite /= IH.
Qed.

Section ChainMaps.
Variable R : pzRingType.
Variables G H : finGroupType.
Variable f : G -> H.

Definition homogeneous_map n :
    {linear homogeneous_term R G n -> homogeneous_term R H n} :=
  free_map R (@vertices_map G H f n.+1).

Lemma homogeneous_map_boundary n (v : homogeneous_term R G n.+1) :
  homogeneous_boundary R H n (homogeneous_map n.+1 v) =
    homogeneous_map n (homogeneous_boundary R G n v).
Proof.
rewrite !homogeneous_boundary_formula linear_sum.
apply: eq_bigr => i _; rewrite linearZ; congr (_ *: _).
rewrite /homogeneous_map -!free_map_composition.
congr (free_map R _ v); apply functional_extensionality_dep => x.
exact: vertices_map_delete.
Qed.

Definition homogeneous_chain_map :
    chain_map (homogeneous_complex R G) (homogeneous_complex R H) :=
  @ChainMap R (homogeneous_complex R G) (homogeneous_complex R H)
    homogeneous_map homogeneous_map_boundary.

Lemma homogeneous_map_augmentation (v : homogeneous_term R G 0) :
  homogeneous_augmentation R H (homogeneous_map 0 v) = homogeneous_augmentation R G v.
Proof.
apply: (free_lift_ext
  (g := (homogeneous_augmentation R H \o homogeneous_map 0 :
    {linear homogeneous_term R G 0 -> R^o}))
  (h := homogeneous_augmentation R G)).
move=> x.
change (homogeneous_augmentation R H (free_map R (@vertices_map G H f 1) (free_basis R x)) =
  homogeneous_augmentation R G (free_basis R x)).
by rewrite free_map_basis !homogeneous_augmentation_basis.
Qed.

End ChainMaps.

Lemma group_path_vertices_natural (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) n b x (p : @path_from (group_category G) n x) :
  path_to_vertices n (f b) x (path_map_from (group_functor f) n x p) =
    vertices_map f n (path_to_vertices n b x p).
Proof.
elim: n b x p => [|n IH] b x p; first reflexivity.
case: p => y [a p].
rewrite /= morphM ?inE //.
by rewrite -(IH (b * a)%g y p) morphM ?inE.
Qed.

Lemma group_homogeneous_generator_natural (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) n x (p : @path_from (group_category G) n.+1 x) :
  @resolution_generator_to_homogeneous H n x
    (path_map_from (group_functor f) n.+1 x p) =
    vertices_map f n.+1 (@resolution_generator_to_homogeneous G n x p).
Proof.
change (@path_to_vertices H n.+1 1%g x (path_map_from (group_functor f) n.+1 x p) =
  vertices_map f n.+1 (@path_to_vertices G n.+1 1%g x p)).
rewrite -(morph1 f); exact: group_path_vertices_natural.
Qed.

Lemma vertices_map_translate (G H : finGroupType)
    (f : {morphism [set: G] >-> H}) n a (v : power G n) :
  vertices_map f n (left_translate n a v) =
    left_translate n (f a) (vertices_map f n v).
Proof.
elim: n v => [|n IH] v; first reflexivity.
by case: v => b v; rewrite /= morphM ?inE // IH.
Qed.

End DPGroupCohomologyHomogeneousMaps.
