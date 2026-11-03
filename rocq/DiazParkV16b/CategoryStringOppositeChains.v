(** The actual signed chain reversal, with literal inverse and augmentation. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category.
From DiazParkV16b Require Import ChainComplex CategoryStringChains CategoryStringOppositeUnsigned.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex.
Local Open Scope ring_scope.

Module DPCategoryStringOppositeChains.
Fixpoint reversal_exponent n : nat :=
  match n with 0%N => 0%N | k.+1 => (reversal_exponent k + k.+1)%N end.

Section Chains.
Variable R : pzRingType.
Variable C : category.

Lemma reversal_sign_succ n :
  (-1 : R) ^+ (reversal_exponent n.+1) * (-1) ^+ n.+1 = (-1) ^+ (reversal_exponent n).
Proof. by rewrite /= exprD -mulrA -expr2 sqrr_sign mulr1. Qed.

Definition reverse_at n (v : category_string_term R C n) : category_string_term R (opposite C) n :=
  (-1) ^+ (reversal_exponent n) *: DPCategoryStringOppositeUnsigned.reverse_at R C n v.
Arguments reverse_at n v : clear implicits.

Lemma reverse_at_linear n : linear (@reverse_at n).
Proof. move=> r v w; by rewrite /reverse_at linearP scalerDr !scalerA commr_sign. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (category_string_term R C n)
  (category_string_term R (opposite C) n) _ (@reverse_at n) (@reverse_at_linear n).

Definition unreverse_at n (v : category_string_term R (opposite C) n) : category_string_term R C n :=
  (-1) ^+ (reversal_exponent n) *: DPCategoryStringOppositeUnsigned.unreverse_at R C n v.
Arguments unreverse_at n v : clear implicits.

Lemma unreverse_at_linear n : linear (@unreverse_at n).
Proof. move=> r v w; by rewrite /unreverse_at linearP scalerDr !scalerA commr_sign. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (category_string_term R (opposite C) n)
  (category_string_term R C n) _ (@unreverse_at n) (@unreverse_at_linear n).

Lemma reverse_inverse n (v : category_string_term R C n) : unreverse_at n (reverse_at n v) = v.
Proof.
by rewrite /unreverse_at /reverse_at linearZ DPCategoryStringOppositeUnsigned.reverse_inverse signrZK.
Qed.

Lemma unreverse_inverse n (v : category_string_term R (opposite C) n) : reverse_at n (unreverse_at n v) = v.
Proof.
by rewrite /unreverse_at /reverse_at linearZ DPCategoryStringOppositeUnsigned.unreverse_inverse signrZK.
Qed.

Lemma reverse_boundary n (v : category_string_term R C n.+1) :
  @category_string_boundary R (opposite C) n (reverse_at n.+1 v) =
  reverse_at n (@category_string_boundary R C n v).
Proof.
rewrite /reverse_at linearZ.
change ((-1) ^+ (reversal_exponent n.+1) *:
  @category_string_boundary R (opposite C) n (DPCategoryStringOppositeUnsigned.reverse_at R C n.+1 v) =
  (-1) ^+ (reversal_exponent n) *: DPCategoryStringOppositeUnsigned.reverse_at R C n
    (@category_string_boundary R C n v)).
by rewrite DPCategoryStringOppositeUnsigned.reverse_boundary scalerA reversal_sign_succ.
Qed.

Lemma unreverse_boundary n (v : category_string_term R (opposite C) n.+1) :
  @category_string_boundary R C n (unreverse_at n.+1 v) =
  unreverse_at n (@category_string_boundary R (opposite C) n v).
Proof.
rewrite /unreverse_at linearZ.
change ((-1) ^+ (reversal_exponent n.+1) *:
  @category_string_boundary R C n (DPCategoryStringOppositeUnsigned.unreverse_at R C n.+1 v) =
  (-1) ^+ (reversal_exponent n) *: DPCategoryStringOppositeUnsigned.unreverse_at R C n
    (@category_string_boundary R (opposite C) n v)).
by rewrite DPCategoryStringOppositeUnsigned.unreverse_boundary scalerA reversal_sign_succ.
Qed.

Definition reverse_chain : chain_map (category_string_chain R C) (category_string_chain R (opposite C)) :=
  @ChainMap R (category_string_chain R C) (category_string_chain R (opposite C))
    (fun n => (@reverse_at n : {linear _ -> _})) reverse_boundary.

Definition unreverse_chain : chain_map (category_string_chain R (opposite C)) (category_string_chain R C) :=
  @ChainMap R (category_string_chain R (opposite C)) (category_string_chain R C)
    (fun n => (@unreverse_at n : {linear _ -> _})) unreverse_boundary.

Lemma reverse_augmentation (v : category_string_term R C 0%N) :
  category_string_augmentation R (opposite C) (reverse_at 0%N v) = category_string_augmentation R C v.
Proof.
rewrite /reverse_at.
change (category_string_augmentation R (opposite C)
  (1 *: DPCategoryStringOppositeUnsigned.reverse_at R C 0%N v) = category_string_augmentation R C v).
by rewrite scale1r DPCategoryStringOppositeUnsigned.reverse_augmentation.
Qed.

Lemma unreverse_augmentation (v : category_string_term R (opposite C) 0%N) :
  category_string_augmentation R C (unreverse_at 0%N v) = category_string_augmentation R (opposite C) v.
Proof.
rewrite /unreverse_at.
change (category_string_augmentation R C
  (1 *: DPCategoryStringOppositeUnsigned.unreverse_at R C 0%N v) = category_string_augmentation R (opposite C) v).
by rewrite scale1r DPCategoryStringOppositeUnsigned.unreverse_augmentation.
Qed.
End Chains.
Arguments reverse_at R C n v : clear implicits.
Arguments unreverse_at R C n v : clear implicits.
End DPCategoryStringOppositeChains.

