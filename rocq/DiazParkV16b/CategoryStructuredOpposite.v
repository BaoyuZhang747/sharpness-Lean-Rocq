(** The genuine structured comma of an opposite functor is the opposite of
    its costructured comma. Both charts preserve the source projection. *)
From DiazPark Require Import Category CategoryComma CategoryIsomorphism.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryStructuredOpposite.
Section Comparison.
Variables C D : category.
Variable F : functor C D.
Variable d : D.
Local Notation X := (opposite (costructured_category F d)).
Local Notation Y := (structured_category (functor_op F) d).

Definition forward_object (x : X) : Y :=
  @Build_costructured_object (opposite (opposite C)) (opposite (opposite D))
    (functor_op (functor_op F)) d (costructured_source x) (costructured_arrow x).

Definition backward_object (y : Y) : X :=
  @Build_costructured_object C D F d (costructured_source y) (costructured_arrow y).

Definition forward_map {x y : X} (f : hom X x y) : hom Y (forward_object x) (forward_object y) :=
  @Build_costructured_hom (opposite (opposite C)) (opposite (opposite D))
    (functor_op (functor_op F)) d (forward_object y) (forward_object x)
    (costructured_map f) (costructured_commutes f).

Definition backward_map {x y : Y} (f : hom Y x y) : hom X (backward_object x) (backward_object y) :=
  @Build_costructured_hom C D F d (backward_object y) (backward_object x)
    (costructured_map f) (costructured_commutes f).

Definition forward : functor X Y.
Proof.
refine (@Build_functor X Y forward_object (fun x y => @forward_map x y) _ _).
- intro x; apply costructured_hom_ext; reflexivity.
- intros x y z f g; apply costructured_hom_ext; reflexivity.
Defined.

Definition backward : functor Y X.
Proof.
refine (@Build_functor Y X backward_object (fun x y => @backward_map x y) _ _).
- intro x; apply costructured_hom_ext; reflexivity.
- intros x y z f g; apply costructured_hom_ext; reflexivity.
Defined.

Definition comma_isomorphism : category_isomorphism X Y.
Proof.
refine (@Build_category_isomorphism X Y forward backward _ _).
- apply (@functor_extensionality X X (functor_comp forward backward) (functor_id X) (eq_refl _)).
  reflexivity.
- apply (@functor_extensionality Y Y (functor_comp backward forward) (functor_id Y) (eq_refl _)).
  reflexivity.
Defined.

Lemma forward_projection :
  functor_comp forward (structured_projection (functor_op F) d) =
    functor_op (costructured_projection F d).
Proof.
apply (@functor_extensionality X (opposite C)
  (functor_comp forward (structured_projection (functor_op F) d))
  (functor_op (costructured_projection F d)) (eq_refl _)); reflexivity.
Qed.
End Comparison.
End DPCategoryStructuredOpposite.
