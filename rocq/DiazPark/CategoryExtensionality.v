(** Equality of natural transformations and the ordinary functor category.
    The foundational principles come from MathComp's classical boolp layer;
    proof irrelevance is derived there from propositional extensionality. They are explicit here,
    rather than hidden in conjecture-specific interfaces. *)

From mathcomp Require Import boolp.
From DiazPark Require Import Category.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma nat_trans_ext {C D : category} {F G : functor C D}
    (a b : nat_trans F G) :
    (forall x, component a x = component b x) -> a = b.
Proof.
  destruct a as [a ha], b as [b hb]. simpl.
  intro h. assert (a = b) as e by (apply functional_extensionality_dep; exact h).
  destruct e. f_equal. apply Prop_irrelevance.
Qed.

Definition functor_category (C D : category) : category.
Proof.
  refine {| object := functor C D;
            hom := @nat_trans C D;
            identity := @nat_id C D;
            compose := fun F G H a b => nat_comp a b |}.
  - intros F G a. apply nat_trans_ext. intro x. apply compose_id_left.
  - intros F G a. apply nat_trans_ext. intro x. apply compose_id_right.
  - intros E F G H a b c. apply nat_trans_ext. intro x. apply compose_assoc.
Defined.

Definition precomposition {B C : category} (D : category) (F : functor B C) :
    functor (functor_category C D) (functor_category B D).
Proof.
  refine (@Build_functor (functor_category C D) (functor_category B D)
    (fun G => functor_comp F G) (fun G H a => nat_whisker_left F a) _ _).
  - intro G. apply nat_trans_ext. intro x. reflexivity.
  - intros G H K a b. apply nat_trans_ext. intro x. reflexivity.
Defined.

Definition postcomposition (B : category) {C D : category} (F : functor C D) :
    functor (functor_category B C) (functor_category B D).
Proof.
  refine (@Build_functor (functor_category B C) (functor_category B D)
    (fun G => functor_comp G F) (fun G H a => nat_whisker_right a F) _ _).
  - intro G. apply nat_trans_ext. intro x. exact (fmap_id F (fobj G x)).
  - intros G H K a b. apply nat_trans_ext. intro x.
    exact (fmap_compose F (component a x) (component b x)).
Defined.
