(** Literal conjugation of categorical endomorphisms along an isomorphism. *)
From DiazPark Require Import Category.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryAutomorphismConjugation.
Section Conjugation.
Variable C : category.

Lemma iso_cancel_left {x y z : C} (e : isomorphism x y) (f g : hom C y z) :
  compose (iso_hom e) f = compose (iso_hom e) g -> f = g.
Proof.
intro h; apply (f_equal (fun t => compose (iso_inv e) t)) in h.
rewrite <- !compose_assoc, iso_inv_hom, !compose_id_left in h; exact h.
Qed.

Definition conjugate {x y : C} (e : isomorphism x y) (a : hom C x x) : hom C y y :=
  compose (iso_inv e) (compose a (iso_hom e)).

Lemma conjugate_intertwines {x y : C} (e : isomorphism x y) (a : hom C x x) :
  compose (iso_hom e) (conjugate e a) = compose a (iso_hom e).
Proof. unfold conjugate; rewrite <- compose_assoc, iso_hom_inv, compose_id_left; reflexivity. Qed.

Lemma conjugate_compose {x y : C} (e : isomorphism x y) (a b : hom C x x) :
  conjugate e (compose a b) = compose (conjugate e a) (conjugate e b).
Proof.
apply (@iso_cancel_left x y y e).
rewrite conjugate_intertwines, <- compose_assoc, conjugate_intertwines,
  !compose_assoc, conjugate_intertwines; reflexivity.
Qed.

Lemma conjugate_square {x x' y y' : C} (e : isomorphism x y) (e' : isomorphism x' y')
    (u : hom C x x') (v : hom C y y') (a : hom C x x) (b : hom C x' x')
    (hu : compose u (iso_hom e') = compose (iso_hom e) v)
    (ha : compose a u = compose u b) :
  compose (conjugate e a) v = compose v (conjugate e' b).
Proof.
apply (@iso_cancel_left x y y' e).
rewrite <- compose_assoc, conjugate_intertwines, compose_assoc, <- hu,
  <- compose_assoc, ha, compose_assoc, <- conjugate_intertwines,
  <- compose_assoc, hu, compose_assoc; reflexivity.
Qed.

Lemma difference_square {x x' y y' : C}
    (a b : isomorphism x y) (a' b' : isomorphism x' y')
    (u : hom C x x') (v : hom C y y')
    (ha : compose u (iso_hom a') = compose (iso_hom a) v)
    (hb : compose u (iso_hom b') = compose (iso_hom b) v) :
  compose (compose (iso_inv a) (iso_hom b)) v =
    compose v (compose (iso_inv a') (iso_hom b')).
Proof.
apply (@iso_cancel_left x y y' a).
rewrite <- !compose_assoc, iso_hom_inv, compose_id_left.
rewrite <- ha, !compose_assoc.
rewrite <- (compose_assoc (iso_hom a') (iso_inv a') (iso_hom b')),
  iso_hom_inv, compose_id_left; exact (eq_sym hb).
Qed.
End Conjugation.
End DPCategoryAutomorphismConjugation.
