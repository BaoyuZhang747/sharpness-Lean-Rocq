(** Pasting two actual pushouts, with the literal comparison arrow. *)
From mathcomp Require Import all_ssreflect.
From DiazPark Require Import Category.
From DiazParkV16b Require Import CategoryPushout.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryPushoutPasting.
Import DPCategoryPushout.

Lemma pushout_hom_ext {C : category} {A B X P Z : C}
  {i : hom C A B} {j : hom C A X} {a : hom C B P} {b : hom C X P}
  (h : pushout_square i j a b) (f g : hom C P Z)
  (ha : compose a f = compose a g) (hb : compose b f = compose b g) : f = g.
Proof.
have w : compose i (compose a g) = compose j (compose b g).
  by rewrite -!compose_assoc (pushout_commutes h).
transitivity (pushout_desc h (compose a g) (compose b g) w).
- exact: pushout_desc_unique.
- symmetry; apply: pushout_desc_unique; reflexivity.
Qed.

Section Pasting.
Context {C : category} {A N B X P Q : C}.
Variables (m : hom C A N) (k : hom C N B) (j : hom C A X).
Variables (a : hom C N P) (b : hom C X P) (c : hom C B Q) (d : hom C X Q).
Variable hN : pushout_square m j a b.
Variable hB : pushout_square (compose m k) j c d.

Lemma pasting_commutes : compose m (compose k c) = compose j d.
Proof. rewrite -compose_assoc; exact: pushout_commutes hB. Qed.

Definition pasting_map : hom C P Q := pushout_desc hN (compose k c) d pasting_commutes.
Lemma pasting_map_left : compose a pasting_map = compose k c.
Proof. exact: pushout_desc_left. Qed.
Lemma pasting_map_right : compose b pasting_map = d.
Proof. exact: pushout_desc_right. Qed.

Section Descent.
Variable Z : C.
Variables (f : hom C B Z) (g : hom C P Z).
Variable w : compose k f = compose a g.

Lemma pasting_desc_commutes : compose (compose m k) f = compose j (compose b g).
Proof. by rewrite compose_assoc w -compose_assoc (pushout_commutes hN) compose_assoc. Qed.
Definition pasting_desc : hom C Q Z := pushout_desc hB f (compose b g) pasting_desc_commutes.
Lemma pasting_desc_left : compose c pasting_desc = f.
Proof. exact: pushout_desc_left. Qed.
Lemma pasting_desc_right : compose pasting_map pasting_desc = g.
Proof.
apply: (pushout_hom_ext hN).
- by rewrite -compose_assoc pasting_map_left compose_assoc pasting_desc_left w.
- rewrite -compose_assoc pasting_map_right; exact: pushout_desc_right.
Qed.
Lemma pasting_desc_unique (s : hom C Q Z) :
  compose c s = f -> compose pasting_map s = g -> s = pasting_desc.
Proof.
move=> hc hp; apply: pushout_desc_unique => //.
by rewrite -pasting_map_right compose_assoc hp.
Qed.
End Descent.

Definition pasting_square : pushout_square k a c pasting_map.
Proof.
refine (@Build_pushout_square C N B P Q k a c pasting_map
  (esym pasting_map_left) (fun Z f g w => pasting_desc w) _ _ _).
- move=> Z f g w; exact: pasting_desc_left.
- move=> Z f g w; exact: pasting_desc_right.
- move=> Z f g w s; exact: pasting_desc_unique.
Defined.

End Pasting.
End DPCategoryPushoutPasting.
