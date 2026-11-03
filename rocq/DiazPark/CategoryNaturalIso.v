(** Pointwise isomorphisms with a proved forward naturality square give an
    actual isomorphism in the ordinary functor category. The inverse
    naturality square is proved, not assumed. *)

From DiazPark Require Import Category CategoryExtensionality.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition nat_iso_of_components {C D : category} {F G : functor C D}
    (e : forall x, isomorphism (fobj F x) (fobj G x))
    (he : forall x y (f : hom C x y),
      compose (fmap F f) (iso_hom (e y)) = compose (iso_hom (e x)) (fmap G f)) :
    @isomorphism (functor_category C D) F G.
Proof.
  unshelve refine (@Build_isomorphism (functor_category C D) F G
    (@Build_nat_trans C D F G (fun x => iso_hom (e x)) he)
    (@Build_nat_trans C D G F (fun x => iso_inv (e x)) _) _ _).
  - intros x y f.
    transitivity (compose (iso_inv (e x))
      (compose (iso_hom (e x)) (compose (fmap G f) (iso_inv (e y))))).
    + rewrite <- compose_assoc, iso_inv_hom, compose_id_left. reflexivity.
    + rewrite <- (compose_assoc (iso_hom (e x)) (fmap G f) (iso_inv (e y))),
        <- (he x y f), compose_assoc, iso_hom_inv, compose_id_right.
      reflexivity.
  - apply nat_trans_ext. intro x. exact (iso_hom_inv (e x)).
  - apply nat_trans_ext. intro x. exact (iso_inv_hom (e x)).
Defined.

Definition nat_iso_component {C D : category} {F G : functor C D}
    (e : @isomorphism (functor_category C D) F G) (x : C) :
    isomorphism (fobj F x) (fobj G x).
Proof.
  refine {| iso_hom := component (iso_hom e) x;
            iso_inv := component (iso_inv e) x |}.
  - exact (f_equal (fun a : nat_trans F F => component a x) (iso_hom_inv e)).
  - exact (f_equal (fun a : nat_trans G G => component a x) (iso_inv_hom e)).
Defined.

Definition evaluation_functor (C D : category) (x : C) :
    functor (functor_category C D) D.
Proof.
  refine (@Build_functor (functor_category C D) D
    (fun F => fobj F x) (fun F G a => component a x) _ _); reflexivity.
Defined.

Arguments evaluation_functor C D x : clear implicits.
