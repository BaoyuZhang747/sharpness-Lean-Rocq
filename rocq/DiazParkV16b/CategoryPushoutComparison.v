(** The canonical comparison isomorphism of two actual pushout squares. *)
From DiazPark Require Import Category.
From DiazParkV16b Require Import CategoryPushout.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryPushoutComparison.
Import DPCategoryPushout.
Section Comparison.
Context {C : category} {A B X Y Z : C}
  {i : hom C A B} {j : hom C A X}
  {k : hom C B Y} {l : hom C X Y}
  {k' : hom C B Z} {l' : hom C X Z}.
Variables (h : pushout_square i j k l) (h' : pushout_square i j k' l').

Definition pushout_comparison : hom C Y Z := pushout_desc h k' l' (pushout_commutes h').

Lemma pushout_comparison_left : compose k pushout_comparison = k'.
Proof. exact (pushout_desc_left h k' l' (pushout_commutes h')). Qed.
Lemma pushout_comparison_right : compose l pushout_comparison = l'.
Proof. exact (pushout_desc_right h k' l' (pushout_commutes h')). Qed.

Lemma pushout_identity_unique (f : hom C Y Y) :
  compose k f = k -> compose l f = l -> f = identity Y.
Proof.
intros hk hl.
transitivity (pushout_desc h k l (pushout_commutes h)).
- exact (pushout_desc_unique h k l (pushout_commutes h) f hk hl).
- symmetry; apply pushout_desc_unique; apply compose_id_right.
Qed.
End Comparison.

Definition pushout_comparison_iso {C : category} {A B X Y Z : C}
  {i : hom C A B} {j : hom C A X}
  {k : hom C B Y} {l : hom C X Y} {k' : hom C B Z} {l' : hom C X Z}
  (h : pushout_square i j k l) (h' : pushout_square i j k' l') : @isomorphism C Y Z.
Proof.
refine (@Build_isomorphism C Y Z (pushout_comparison h h') (pushout_comparison h' h) _ _).
- apply (pushout_identity_unique h).
  + rewrite <- compose_assoc, !pushout_comparison_left. reflexivity.
  + rewrite <- compose_assoc, !pushout_comparison_right. reflexivity.
- apply (pushout_identity_unique h').
  + rewrite <- compose_assoc, !pushout_comparison_left. reflexivity.
  + rewrite <- compose_assoc, !pushout_comparison_right. reflexivity.
Defined.
End DPCategoryPushoutComparison.
