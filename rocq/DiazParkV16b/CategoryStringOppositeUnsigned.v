(** Unsigned string reversal and its exact alternating-boundary sign. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarPaths BarFreeModule.
From DiazParkV16b Require Import CategoryStringChains CategoryStringOppositePaths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPCategoryStringOppositePaths.
Local Open Scope ring_scope.

Module DPCategoryStringOppositeUnsigned.
Section Chains.
Variable R : pzRingType.
Variable C : category.

Definition reverse_at n : {linear category_string_term R C n -> category_string_term R (opposite C) n} :=
  free_map R (@reverse_path C n).

Definition unreverse_at n : {linear category_string_term R (opposite C) n -> category_string_term R C n} :=
  free_map R (@unreverse_path C n).

Lemma reverse_inverse n (v : category_string_term R C n) : unreverse_at n (reverse_at n v) = v.
Proof.
apply (free_lift_ext (g := (unreverse_at n \o reverse_at n : {linear _ -> _}))
  (h := (idfun : {linear _ -> _}))).
move=> s; by rewrite /= /reverse_at /unreverse_at !free_map_basis reverse_path_inverse.
Qed.

Lemma unreverse_inverse n (v : category_string_term R (opposite C) n) : reverse_at n (unreverse_at n v) = v.
Proof.
apply (free_lift_ext (g := (reverse_at n \o unreverse_at n : {linear _ -> _}))
  (h := (idfun : {linear _ -> _}))).
move=> s; by rewrite /= /reverse_at /unreverse_at !free_map_basis unreverse_path_inverse.
Qed.

Lemma reverse_face n (i : 'I_n.+2) (v : category_string_term R C n.+1) :
  reverse_at n (@category_string_face R C n i v) =
  @category_string_face R (opposite C) n (rev_ord i) (reverse_at n.+1 v).
Proof.
apply (free_lift_ext
  (g := (reverse_at n \o @category_string_face R C n i : {linear _ -> _}))
  (h := (@category_string_face R (opposite C) n (rev_ord i) \o reverse_at n.+1 : {linear _ -> _}))).
move=> s; by rewrite /= /reverse_at /category_string_face !free_map_basis reverse_path_face.
Qed.

Lemma reverse_sign n (i : 'I_n.+2) :
  (-1 : R) ^+ (rev_ord i) = (-1) ^+ n.+1 * (-1) ^+ i.
Proof.
have he : (val (rev_ord i) + i = n.+1)%N.
  change (n.+2 - i.+1 + i = n.+1)%N; rewrite subSS.
  apply subnK; by rewrite -ltnS; exact: ltn_ord.
have hs : (-1 : R) ^+ n.+1 = (-1) ^+ (rev_ord i) * (-1) ^+ i.
  by rewrite -exprD he.
by rewrite hs -mulrA -expr2 sqrr_sign mulr1.
Qed.

Lemma reverse_boundary n (v : category_string_term R C n.+1) :
  @category_string_boundary R (opposite C) n (reverse_at n.+1 v) =
  (-1) ^+ n.+1 *: reverse_at n (@category_string_boundary R C n v).
Proof.
rewrite /category_string_boundary [LHS](reindex_inj (@rev_ord_inj n.+2)).
rewrite linear_sum scaler_sumr; apply eq_bigr=> i _.
by rewrite linearZ reverse_face reverse_sign scalerA.
Qed.

Lemma unreverse_boundary n (v : category_string_term R (opposite C) n.+1) :
  @category_string_boundary R C n (unreverse_at n.+1 v) =
  (-1) ^+ n.+1 *: unreverse_at n (@category_string_boundary R (opposite C) n v).
Proof.
apply (can_inj (@reverse_inverse n)).
rewrite linearZ unreverse_inverse.
have h := reverse_boundary (unreverse_at n.+1 v).
rewrite unreverse_inverse in h.
rewrite h.
change (reverse_at n (@category_string_boundary R C n (unreverse_at n.+1 v)) =
  (-1) ^+ n.+1 *: ((-1) ^+ n.+1 *:
    reverse_at n (@category_string_boundary R C n (unreverse_at n.+1 v)))).
by rewrite signrZK.
Qed.

Lemma reverse_augmentation (v : category_string_term R C 0%N) :
  category_string_augmentation R (opposite C) (reverse_at 0%N v) = category_string_augmentation R C v.
Proof.
apply (free_lift_ext
  (g := (category_string_augmentation R (opposite C) \o reverse_at 0%N : {linear _ -> _}))
  (h := category_string_augmentation R C)).
move=> s; by rewrite /= /reverse_at free_map_basis !category_string_augmentation_basis.
Qed.

Lemma unreverse_augmentation (v : category_string_term R (opposite C) 0%N) :
  category_string_augmentation R C (unreverse_at 0%N v) = category_string_augmentation R (opposite C) v.
Proof. by rewrite -reverse_augmentation unreverse_inverse. Qed.
End Chains.
End DPCategoryStringOppositeUnsigned.


