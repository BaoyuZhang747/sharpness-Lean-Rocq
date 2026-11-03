From Stdlib Require Import Arith.PeanoNat Lia.
From mathcomp Require Import all_ssreflect boolp.
From DiazParkV16b Require Import SimplexCategory.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplexOperators.
Import DPSimplexCategory.

Definition coface_value (i j : nat) :=
  if Nat.leb i j then S j else j.

Definition codegeneracy_value (i j : nat) :=
  if Nat.ltb i j then Nat.pred j else j.

Lemma coface_value_bound n (i : 'I_n.+2) (j : 'I_n.+1) :
  (coface_value i j < n.+2)%N.
Proof.
  apply/ltP.
  have hbound : (val j < n.+1)%coq_nat := (elimT ltP (ltn_ord j)).
  unfold coface_value. destruct (Nat.leb i j); cbn in *; lia.
Qed.

Definition coface n (i : 'I_n.+2) : ordinal_map n n.+1.
Proof.
  refine (@OrdinalMap n n.+1
    (fun j => @Ordinal n.+2 (coface_value i j) (coface_value_bound i j)) _).
  intros j k hjk. apply/leP.
  have h : (val j <= val k)%coq_nat := elimT leP hjk.
  change (coface_value i j <= coface_value i k)%coq_nat.
  unfold coface_value.
  destruct (Nat.leb_spec0 i j); destruct (Nat.leb_spec0 i k); cbn in *; lia.
Defined.

Arguments coface {_} _.

Lemma codegeneracy_value_bound n (i : 'I_n.+1) (j : 'I_n.+2) :
  (codegeneracy_value i j < n.+1)%N.
Proof.
  apply/ltP.
  have hi : (val i < n.+1)%coq_nat := elimT ltP (ltn_ord i).
  have hj : (val j < n.+2)%coq_nat := elimT ltP (ltn_ord j).
  unfold codegeneracy_value. destruct (Nat.ltb_spec0 i j); cbn in *; lia.
Qed.

Definition codegeneracy n (i : 'I_n.+1) : ordinal_map n.+1 n.
Proof.
  refine (@OrdinalMap n.+1 n
    (fun j => @Ordinal n.+1 (codegeneracy_value i j)
      (codegeneracy_value_bound i j)) _).
  intros j k hjk. apply/leP.
  have h : (val j <= val k)%coq_nat := elimT leP hjk.
  change (codegeneracy_value i j <= codegeneracy_value i k)%coq_nat.
  unfold codegeneracy_value.
  destruct (Nat.ltb_spec0 i j); destruct (Nat.ltb_spec0 i k); cbn in *; lia.
Defined.

Arguments codegeneracy {_} _.

Lemma coface_apply n (i : 'I_n.+2) (j : 'I_n.+1) :
  val (coface i j) = coface_value i j.
Proof. reflexivity. Qed.

Lemma codegeneracy_apply n (i : 'I_n.+1) (j : 'I_n.+2) :
  val (codegeneracy i j) = codegeneracy_value i j.
Proof. reflexivity. Qed.

End DPSimplexOperators.
