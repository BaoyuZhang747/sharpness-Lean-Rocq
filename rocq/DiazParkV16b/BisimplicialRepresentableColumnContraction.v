(** The vertical columns of a representable contract to their actual free module of horizontal simplices. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialChains ChainComplex
  BisimplicialSet BisimplicialChains BisimplicialRepresentable StandardSimplexCone
  StandardSimplexConeChains SimplicialConeContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplexCategory DPSimplicialSet DPSimplicialChains
  DPChainComplex DPBisimplicialSet DPBisimplicialChains DPBisimplicialRepresentable
  DPStandardSimplexCone DPStandardSimplexConeChains DPSimplicialConeContraction.
Local Open Scope ring_scope.

Module DPBisimplicialRepresentableColumnContraction.
Section Model.
Variables m n p : nat.
Let X := representable_row m n p.
Definition column_cone q (x : simplex X q) : simplex X q.+1 := (x.1, cone x.2).
Lemma column_cone_zero q x : @indexed_face X q 0 (column_cone x) = x.
Proof.
case: x => a b.
change ((a,@indexed_face (standard_simplex n) q 0 (cone b)) = (a,b)).
by rewrite indexed_cone_zero.
Qed.
Lemma column_cone_successor q (i : 'I_q.+2) x :
  @indexed_face X q.+1 i.+1 (column_cone x) = column_cone (@indexed_face X q i x).
Proof.
case: x => a b.
change ((a,@indexed_face (standard_simplex n) q.+1 i.+1 (cone b)) =
  (a,cone (@indexed_face (standard_simplex n) q i b))).
by rewrite indexed_cone_successor.
Qed.
Lemma column_cone_last x : @indexed_face X 0 1 (column_cone x) = (x.1,zero_vertex n).
Proof.
case: x => a b.
change ((a,@indexed_face (standard_simplex n) 0 1 (cone b)) = (a,zero_vertex n)).
by rewrite indexed_cone_last_zero.
Qed.

Variable R : pzRingType.
Definition column_augmentation : {linear term R X 0%N -> free_module R (ordinal_map p m)} := free_map R fst.
Definition column_augmentation_section : {linear free_module R (ordinal_map p m) -> term R X 0%N} :=
  free_map R (fun a => (a,zero_vertex n)).
Lemma column_augmentation_basis (x : simplex X 0%N) :
  column_augmentation (free_basis R x) = free_basis R x.1.
Proof. exact: free_map_basis. Qed.
Lemma column_augmentation_sectionK a : column_augmentation (column_augmentation_section a) = a.
Proof.
apply: (free_lift_ext (g := (column_augmentation \o column_augmentation_section : {linear _ -> _}))
  (h := (idfun : {linear free_module R (ordinal_map p m) -> _}))).
move=> x; rewrite /= /column_augmentation_section free_map_basis column_augmentation_basis; reflexivity.
Qed.
Lemma column_cone_last_basis x :
  free_basis R (@indexed_face X 0 1 (column_cone x)) =
    column_augmentation_section (column_augmentation (free_basis R x)).
Proof. by rewrite column_cone_last column_augmentation_basis /column_augmentation_section free_map_basis. Qed.
Theorem column_augmentation_boundary a : column_augmentation (@DPSimplicialChains.boundary R X 0 a) = 0.
Proof.
pose f : {linear term R X 1%N -> free_module R (ordinal_map p m)} :=
  (column_augmentation \o @DPSimplicialChains.boundary R X 0 : {linear _ -> _}).
change (f a = 0).
rewrite -[in LHS](free_basis_generation a) linear_sum.
apply big1_seq => x _; rewrite linearZ.
suff hz : f (free_basis R x) = 0 by rewrite hz; exact: scaler0.
case: x => u v.
change (column_augmentation (@DPSimplicialChains.boundary R X 0 (free_basis R (u,v))) = 0).
rewrite /DPSimplicialChains.boundary !big_ord_recl big_ord0 expr0 expr1 scale1r scaleN1r addr0
  linearB /face_map !free_map_basis.
change (free_basis R u - free_basis R u = 0); exact: subrr.
Qed.
Theorem representable_column_positive_exact q (a : chain_term (chains R X) q.+1) :
  @cycle R (chains R X) q.+1 a -> @DPChainComplex.boundary R (chains R X) q.+1 a.
Proof. exact (@cone_positive_exact R X (@column_cone) column_cone_zero column_cone_successor q a). Qed.
Theorem representable_column_augmentation_exact (a : term R X 0%N) :
  column_augmentation a = 0 -> @DPChainComplex.boundary R (chains R X) 0 a.
Proof. exact (@cone_augmentation_exact R X (@column_cone) column_cone_zero
  (free_module R (ordinal_map p m)) column_augmentation column_augmentation_section column_cone_last_basis a). Qed.
End Model.
End DPBisimplicialRepresentableColumnContraction.
