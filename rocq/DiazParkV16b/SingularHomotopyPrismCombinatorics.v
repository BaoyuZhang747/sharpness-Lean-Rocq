(** The interval-coordinate identities of the standard staircase prism. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From mathcomp Require Import all_ssreflect boolp.
From DiazParkV16b Require Import SimplexCategoryOperators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSingularPrismCombinatorics.
Import DPSimplexOperators.

Definition prism_time_value i k := Nat.ltb i k.

Lemma prism_time_first k : prism_time_value 0 (coface_value 0 k) = true.
Proof. unfold prism_time_value, coface_value; simpl. reflexivity. Qed.

Lemma prism_time_last n k : (k <= n)%coq_nat ->
  prism_time_value n (coface_value (S n) k) = false.
Proof.
intro h; unfold prism_time_value, coface_value.
destruct (Nat.leb_spec0 (S n) k); [lia|].
apply Nat.ltb_ge; lia.
Qed.

Lemma prism_time_middle i k :
  prism_time_value i (coface_value (S i) k) =
    prism_time_value (S i) (coface_value (S i) k).
Proof.
unfold prism_time_value, coface_value.
destruct (Nat.leb_spec0 (S i) k);
  repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec0 a b) end;
  try reflexivity; lia.
Qed.

Lemma prism_time_left i j k : (j <= i)%coq_nat ->
  prism_time_value (S i) (coface_value j k) = prism_time_value i k.
Proof.
intro h; unfold prism_time_value, coface_value.
destruct (Nat.leb_spec0 j k);
  repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec0 a b) end;
  try reflexivity; lia.
Qed.

Lemma prism_time_right i j k : (i <= j)%coq_nat ->
  prism_time_value i (coface_value (S (S j)) k) = prism_time_value i k.
Proof.
intro h; unfold prism_time_value, coface_value.
destruct (Nat.leb_spec0 (S (S j)) k);
  repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec0 a b) end;
  try reflexivity; lia.
Qed.

End DPSingularPrismCombinatorics.
