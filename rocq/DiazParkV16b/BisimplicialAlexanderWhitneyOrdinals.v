(** Literal front/back ordinal maps and every face identity in Alexander--Whitney. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From mathcomp Require Import all_ssreflect boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplexOperators DPSimplexIdentities.

Module DPAlexanderWhitneyOrdinals.
Lemma front_bound p q n (h : Nat.add p q = n) (i : 'I_p.+1) : (val i < n.+1)%N.
Proof. apply/ltP; have hi : (val i < p.+1)%coq_nat := elimT ltP (ltn_ord i); lia. Qed.
Definition front (p q n : nat) (h : Nat.add p q = n) : ordinal_map p n.
Proof.
refine (@OrdinalMap p n (fun i => @Ordinal n.+1 (val i) (front_bound h i)) _).
move=> i j hij; exact hij.
Defined.
Arguments front p q n h : clear implicits.
Lemma front_value p q n h i : val (front p q n h i) = val i.
Proof. reflexivity. Qed.

Lemma back_bound p q n (h : Nat.add p q = n) (i : 'I_q.+1) : (Nat.add p (val i) < n.+1)%N.
Proof. apply/ltP; have hi : (val i < q.+1)%coq_nat := elimT ltP (ltn_ord i); lia. Qed.
Definition back (p q n : nat) (h : Nat.add p q = n) : ordinal_map q n.
Proof.
refine (@OrdinalMap q n (fun i => @Ordinal n.+1 (Nat.add p (val i)) (back_bound h i)) _).
move=> i j hij; apply/leP; have hij' : (val i <= val j)%coq_nat := elimT leP hij; cbn in *; lia.
Defined.
Arguments back p q n h : clear implicits.
Lemma back_value p q n h i : val (back p q n h i) = Nat.add p (val i).
Proof. reflexivity. Qed.

Lemma successor_left p q n : Nat.add p q = n -> Nat.add p.+1 q = n.+1.
Proof. lia. Qed.
Lemma successor_right p q n : Nat.add p q = n -> Nat.add p q.+1 = n.+1.
Proof. lia. Qed.

Definition early_index p q n (h : Nat.add p q = n) (i : 'I_p.+1) : 'I_n.+2.
Proof. refine (@Ordinal n.+2 (val i) _); apply/ltP; have hi : (val i < p.+1)%coq_nat := elimT ltP (ltn_ord i); lia. Defined.
Arguments early_index p q n h i : clear implicits.
Definition late_index p q n (h : Nat.add p q = n) (j : 'I_q.+1) : 'I_n.+2.
Proof. refine (@Ordinal n.+2 (Nat.add p.+1 (val j)) _); apply/ltP; have hj : (val j < q.+1)%coq_nat := elimT ltP (ltn_ord j); lia. Defined.
Arguments late_index p q n h j : clear implicits.

Lemma front_early p q n (h : Nat.add p q = n) (i : 'I_p.+1) :
  ordinal_map_compose (front p q n h) (coface (early_index p q n h i)) =
  ordinal_map_compose (coface (vertex_widen i)) (front p.+1 q n.+1 (successor_left h)).
Proof.
apply ordinal_map_ext => k; apply val_inj.
change (coface_value (val i) (val k) = coface_value (val i) (val k)).
reflexivity.
Qed.

Lemma back_early p q n (h : Nat.add p q = n) (i : 'I_p.+1) :
  ordinal_map_compose (back p q n h) (coface (early_index p q n h i)) =
  back p.+1 q n.+1 (successor_left h).
Proof.
apply ordinal_map_ext => k; apply val_inj.
change (coface_value (val i) (Nat.add p (val k)) = Nat.add p.+1 (val k)).
have hi : (val i < p.+1)%coq_nat := elimT ltP (ltn_ord i); ordinal_arithmetic.
Qed.

Lemma front_late p q n (h : Nat.add p q = n) (j : 'I_q.+1) :
  ordinal_map_compose (front p q n h) (coface (late_index p q n h j)) =
  front p q.+1 n.+1 (successor_right h).
Proof.
apply ordinal_map_ext => k; apply val_inj.
change (coface_value (Nat.add p.+1 (val j)) (val k) = val k).
have hk : (val k < p.+1)%coq_nat := elimT ltP (ltn_ord k); ordinal_arithmetic.
Qed.

Lemma back_late p q n (h : Nat.add p q = n) (j : 'I_q.+1) :
  ordinal_map_compose (back p q n h) (coface (late_index p q n h j)) =
  ordinal_map_compose (coface (vertex_successor j)) (back p q.+1 n.+1 (successor_right h)).
Proof.
apply ordinal_map_ext => k; apply val_inj.
change (coface_value (Nat.add p.+1 (val j)) (Nat.add p (val k)) =
  Nat.add p (coface_value (val j).+1 (val k))).
ordinal_arithmetic.
Qed.

Lemma front_middle p q n (h : Nat.add p q = n) :
  ordinal_map_compose (coface (ord_max : 'I_p.+2)) (front p.+1 q n.+1 (successor_left h)) =
  front p q.+1 n.+1 (successor_right h).
Proof.
apply ordinal_map_ext => k; apply val_inj.
change (coface_value p.+1 (val k) = val k).
have hk : (val k < p.+1)%coq_nat := elimT ltP (ltn_ord k); ordinal_arithmetic.
Qed.

Lemma back_middle p q n (h : Nat.add p q = n) :
  ordinal_map_compose (coface (ord0 : 'I_q.+2)) (back p q.+1 n.+1 (successor_right h)) =
  back p.+1 q n.+1 (successor_left h).
Proof.
apply ordinal_map_ext => k; apply val_inj.
change (Nat.add p (coface_value 0%N (val k)) = Nat.add p.+1 (val k)).
ordinal_arithmetic.
Qed.
End DPAlexanderWhitneyOrdinals.
