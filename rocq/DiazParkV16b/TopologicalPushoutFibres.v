(** Exact underlying fibres of an attachment along an injective map. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalPushoutCarrier.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPTopologicalPushoutFibres.
Import DPTopological DPTopologicalPushoutCarrier.
Section Fibres.
Variables A B X : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X).
Hypothesis hi : injective i.

Definition attachment_normal_left (b : B) : X + B :=
  match pselect (exists a, i a = b) with
  | left h => inl (j (proj1_sig (constructive_indefinite_description h)))
  | right _ => inr b
  end.

Lemma attachment_normal_left_glue a : attachment_normal_left (i a) = inl (j a).
Proof.
rewrite /attachment_normal_left; case: pselect => h.
- have ha := proj2_sig (constructive_indefinite_description h).
  have -> : proj1_sig (constructive_indefinite_description h) = a := hi ha.
  reflexivity.
- exfalso; apply h; by exists a.
Qed.

Lemma attachment_normal_left_cross b x :
  attachment_normal_left b = inl x <-> exists a, i a = b /\ j a = x.
Proof.
rewrite /attachment_normal_left; case: pselect => h.
- split.
  + move=> e; exists (proj1_sig (constructive_indefinite_description h)); split.
    * exact: (proj2_sig (constructive_indefinite_description h)).
    * by injection e.
  + move=> [a [ea ex]].
    have ep := proj2_sig (constructive_indefinite_description h).
    have -> : proj1_sig (constructive_indefinite_description h) = a := hi (etrans ep (esym ea)).
    by rewrite ex.
- split; first by discriminate.
  move=> [a [ea _]]; exfalso; apply h; by exists a.
Qed.

Definition attachment_normal (p : attaching_raw B X) : X + B :=
  match p with
  | @existT _ _ true b => attachment_normal_left b
  | @existT _ _ false x => inl x
  end.

Lemma attachment_normal_equivalent p q : attaching_equivalent i j p q ->
  attachment_normal p = attachment_normal q.
Proof.
move=> h; elim: h => [p0|p0 q0 h ih|p0 q0 r0 h ih k ih'|a].
- reflexivity.
- exact: esym ih.
- exact: etrans ih ih'.
- exact: attachment_normal_left_glue.
Qed.

Lemma attaching_right_injective : injective (attaching_right i j).
Proof.
move=> x y /attaching_class_eq h.
have e := attachment_normal_equivalent h. by injection e.
Qed.

Lemma attaching_left_right b x :
  attaching_left i j b = attaching_right i j x <-> exists a, i a = b /\ j a = x.
Proof.
split.
- move=> /attaching_class_eq h; apply/attachment_normal_left_cross.
  exact: attachment_normal_equivalent h.
- move=> [a [<- <-]]; apply/attaching_class_eq; exact: attaching_glue.
Qed.

Lemma attaching_left_fibres b b' :
  attaching_left i j b = attaching_left i j b' <->
    b = b' \/ exists a a', i a = b /\ i a' = b' /\ j a = j a'.
Proof.
split.
- move=> /attaching_class_eq h.
  have e := attachment_normal_equivalent h.
  change (attachment_normal_left b = attachment_normal_left b') in e.
  clear h. move: e; rewrite /attachment_normal_left; case: pselect => h; case: pselect => h'.
  + move=> e; right.
    exists (proj1_sig (constructive_indefinite_description h)),
      (proj1_sig (constructive_indefinite_description h')).
    split; first exact: (proj2_sig (constructive_indefinite_description h)).
    split; first exact: (proj2_sig (constructive_indefinite_description h')).
    by injection e.
  + by discriminate.
  + by discriminate.
  + move=> e; left; by injection e.
- case=> [->|[a [a' [<- [<- e]]]]]; first reflexivity.
  apply/attaching_class_eq.
  apply: (@attaching_trans _ _ _ i j _ (raw_right B (j a)) _).
  + exact: attaching_glue.
  + rewrite e; apply attaching_sym; exact: attaching_glue.
Qed.

Lemma attaching_left_outside_fibre b (hb : ~ exists a, i a = b) b' :
  attaching_left i j b' = attaching_left i j b <-> b' = b.
Proof.
rewrite attaching_left_fibres; split.
- case=> [e|[a [a' [_ [ha' _]]]]].
  + exact e.
  + exfalso; apply hb; by exists a'.
- by move=> ->; left.
Qed.

End Fibres.
End DPTopologicalPushoutFibres.
