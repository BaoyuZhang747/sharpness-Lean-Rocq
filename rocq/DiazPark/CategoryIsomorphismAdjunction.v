(** A literal category isomorphism yields an actual adjunction. The unit,
    counit and both triangles are constructed from equality transport. *)
From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryAdjunction CategoryIsomorphism CategoryFibration.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition functor_equality_transformation {C D : category} {F G : functor C D}
    (h : F = G) : nat_trans F G :=
  match h with eq_refl => nat_id F end.

Lemma functor_equality_component {C D : category} {F G : functor C D}
    (h : F = G) (x : C) :
    component (functor_equality_transformation h) x =
      equality_arrow (f_equal (fun K : functor C D => fobj K x) h).
Proof. destruct h. reflexivity. Qed.

Lemma fmap_equality_arrow {C D : category} (F : functor C D) {x y : C} (h : x = y) :
    fmap F (equality_arrow h) = equality_arrow (f_equal (fobj F) h).
Proof. destruct h. exact (fmap_id F x). Qed.

Lemma equality_arrow_loop {C : category} (x : C) (h : x = x) :
    equality_arrow h = identity x.
Proof. replace h with (eq_refl x) by apply Prop_irrelevance. reflexivity. Qed.

Definition category_iso_adjunction {C D : category} (e : category_isomorphism C D) :
    adjunction (category_iso_forward e) (category_iso_backward e).
Proof.
refine (@Build_adjunction C D (category_iso_forward e) (category_iso_backward e)
  (functor_equality_transformation (eq_sym (category_iso_forward_backward e)))
  (functor_equality_transformation (category_iso_backward_forward e)) _ _).
- intro x. rewrite !functor_equality_component, fmap_equality_arrow, equality_arrow_comp.
  apply equality_arrow_loop.
- intro y. rewrite !functor_equality_component, fmap_equality_arrow, equality_arrow_comp.
  apply equality_arrow_loop.
Defined.
