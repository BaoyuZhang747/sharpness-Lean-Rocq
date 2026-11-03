(** The actual comparison between two conjugation maps is an intertwiner. *)
From DiazPark Require Import Category.
From DiazParkV16b Require Import CategoryAutomorphismConjugation.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryAutomorphismConjugation.

Module DPCategoryAutomorphismComparison.
Section Comparison.
Variable C : category.
Variables x y : C.
Variables e f : isomorphism x y.

Lemma difference_intertwines :
  compose (iso_hom e) (compose (iso_inv e) (iso_hom f)) = iso_hom f.
Proof. rewrite <- compose_assoc, iso_hom_inv, compose_id_left; reflexivity. Qed.

Lemma conjugate_difference_intertwines (a : hom C x x) :
  compose (conjugate e a) (compose (iso_inv e) (iso_hom f)) =
    compose (compose (iso_inv e) (iso_hom f)) (conjugate f a).
Proof.
apply (@iso_cancel_left C x y y e).
rewrite <- compose_assoc, conjugate_intertwines, compose_assoc,
  difference_intertwines, <- compose_assoc, difference_intertwines,
  conjugate_intertwines; reflexivity.
Qed.
End Comparison.
End DPCategoryAutomorphismComparison.
