(** Explicit contraction of the image of an actual constant functor on
    unnormalized category-string chains, including its augmentation. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarPaths BarFreeModule.
From DiazParkV16b Require Import ChainComplex CategoryBarPullbackPaths
  CategoryStringChains CategoryStringChainsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule DPChainComplex DPCategoryBarPullback.
Local Open Scope ring_scope.

Module DPCategoryStringConstant.
Section Constant.
Variables C D : category.
Variable b : D.

Definition constant_functor : functor C D.
Proof.
refine (@Build_functor C D (fun _ => b) (fun _ _ _ => identity b) _ _).
- reflexivity.
- intros; symmetry; exact: compose_id_left.
Defined.

Fixpoint constant_path_from n : @path_from D n b :=
  match n with 0%N => tt | k.+1 => existT _ b (identity b, constant_path_from k) end.

Definition constant_path n : @path D n := existT _ b (constant_path_from n).

Lemma constant_inner_face n i :
  @path_inner_face D n i b (constant_path_from n.+1) = constant_path_from n.
Proof.
elim: n i=> [|n ih] i; first reflexivity.
case: i=> [|i]; simpl; first by rewrite compose_id_left.
by rewrite ih.
Qed.

Lemma constant_face n i : @path_face D n i (constant_path n.+1) = constant_path n.
Proof. case: i=> [|i]; first reflexivity. by rewrite /path_face /path_remove_inner /constant_path constant_inner_face. Qed.

Lemma constant_map_from n x (s : @path_from C n x) :
  path_map_from constant_functor n x s = constant_path_from n.
Proof.
elim: n x s=> [|n ih] x s; first reflexivity.
case: s=> y [f q]; simpl; by rewrite ih.
Qed.

Lemma constant_map n (s : @path C n) : path_map constant_functor n s = constant_path n.
Proof. case: s=> x q; rewrite /path_map /constant_path; congr (existT _ b _); exact: constant_map_from. Qed.

Variable R : pzRingType.
Definition insert_at n : {linear category_string_term R C n -> category_string_term R D n.+1} :=
  free_map R (fun _ : @path C n => constant_path n.+1).

Lemma insert_face_zero n (a : category_string_term R C n) :
  @category_string_face R D n 0 (insert_at n a) = category_string_map_at R constant_functor n a.
Proof.
apply (free_lift_ext
  (g := (@category_string_face R D n 0 \o insert_at n : {linear _ -> _}))
  (h := category_string_map_at R constant_functor n)).
move=> s; rewrite /= /insert_at /category_string_face /category_string_map_at !free_map_basis.
by rewrite constant_map.
Qed.

Lemma insert_face_succ n i (a : category_string_term R C n.+1) :
  @category_string_face R D n.+1 i.+1 (insert_at n.+1 a) =
    insert_at n (@category_string_face R C n i a).
Proof.
apply (free_lift_ext
  (g := (@category_string_face R D n.+1 i.+1 \o insert_at n.+1 : {linear _ -> _}))
  (h := (insert_at n \o @category_string_face R C n i : {linear _ -> _}))).
move=> s; rewrite /= /insert_at /category_string_face !free_map_basis.
change (free_basis R (@path_face D n.+1 i.+1 (constant_path n.+2)) =
  free_basis R (constant_path n.+1)).
by rewrite constant_face.
Qed.

Theorem constant_contraction_successor n (a : category_string_term R C n.+1) :
  @category_string_boundary R D n.+1 (insert_at n.+1 a) +
    insert_at n (@category_string_boundary R C n a) =
  category_string_map_at R constant_functor n.+1 a.
Proof.
rewrite /category_string_boundary big_ord_recl expr0 scale1r insert_face_zero linear_sum.
have he : \sum_(i < n.+2) (-1) ^+ i.+1 *:
    @category_string_face R D n.+1 i.+1 (insert_at n.+1 a) =
    - (\sum_(i < n.+2) insert_at n ((-1) ^+ i *: @category_string_face R C n i a)).
  rewrite -sumrN; apply eq_bigr=> i _.
  by rewrite insert_face_succ linearZ exprS mulN1r scaleNr.
by rewrite he subrK.
Qed.

Lemma constant_zero_augmentation (a : category_string_term R C 0%N) :
  category_string_map_at R constant_functor 0%N a =
    (category_string_augmentation R C a : R) *:
      (free_basis R (constant_path 0%N) : category_string_term R D 0%N).
Proof.
rewrite -[a](free_basis_generation a) !linear_sum scaler_suml.
apply eq_bigr=> s _.
rewrite !linearZ /category_string_map_at free_map_basis constant_map.
rewrite category_string_augmentation_basis /=.
change ((free_coefficient a s : R) *: free_basis R (constant_path 0%N) =
  ((free_coefficient a s : R) * 1) *: free_basis R (constant_path 0%N)).
by rewrite mulr1.
Qed.

Lemma constant_positive_boundary n (a : category_string_term R C n.+1) :
  @category_string_boundary R C n a = 0 ->
  exists w, @category_string_boundary R D n.+1 w = category_string_map_at R constant_functor n.+1 a.
Proof.
move=> ha; exists (insert_at n.+1 a); have h := constant_contraction_successor a.
by rewrite ha linear0 addr0 in h.
Qed.
End Constant.
End DPCategoryStringConstant.
