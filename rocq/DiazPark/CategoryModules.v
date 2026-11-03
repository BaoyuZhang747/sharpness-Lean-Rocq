(** The ordinary category of arbitrary MathComp modules.
    Morphisms are functions with the genuine MathComp linearity predicate.
    This representation makes the proof-irrelevance step explicit and does
    not impose finite dimension, finite generation or finite carriers. *)

From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition module_hom (R : pzRingType) (U V : lmodType R) :=
  {f : U -> V | linear f}.

Arguments module_hom {R} U V.

Definition module_hom_fun {R : pzRingType} {U V : lmodType R}
    (f : module_hom U V) : U -> V := proj1_sig f.

Coercion module_hom_fun : module_hom >-> Funclass.

Lemma module_hom_linear {R : pzRingType} {U V : lmodType R}
    (f : module_hom U V) : linear f.
Proof. exact (proj2_sig f). Qed.

Lemma module_hom_add {R : pzRingType} {U V : lmodType R}
    (f : module_hom U V) (x y : U) : f (x + y) = f x + f y.
Proof.
  have h := module_hom_linear f 1 x y.
  by rewrite !scale1r in h.
Qed.

Lemma module_hom_sub {R : pzRingType} {U V : lmodType R}
    (f : module_hom U V) (x y : U) : f (x - y) = f x - f y.
Proof. exact: (GRing.zmod_morphism_linear (module_hom_linear f)). Qed.

Lemma module_hom_zero {R : pzRingType} {U V : lmodType R}
    (f : module_hom U V) : f 0 = 0.
Proof.
  have h := module_hom_sub f 0 0.
  by rewrite !subrr in h.
Qed.

Lemma module_hom_neg {R : pzRingType} {U V : lmodType R}
    (f : module_hom U V) (x : U) : f (- x) = - f x.
Proof.
  have h := module_hom_sub f 0 x.
  by rewrite sub0r module_hom_zero sub0r in h.
Qed.

Lemma module_hom_scale {R : pzRingType} {U V : lmodType R}
    (f : module_hom U V) (a : R) (x : U) : f (a *: x) = a *: f x.
Proof. exact: (GRing.scalable_linear (module_hom_linear f)). Qed.

Lemma module_hom_ext {R : pzRingType} {U V : lmodType R}
    (f g : module_hom U V) : (forall x, f x = g x) -> f = g.
Proof.
  destruct f as [f hf], g as [g hg]. simpl.
  intro h. assert (f = g) as e by (apply funext; exact h).
  destruct e. f_equal. apply Prop_irrelevance.
Qed.

Definition module_hom_id {R : pzRingType} (U : lmodType R) : module_hom U U.
Proof. exists (@idfun U). intros a x y. reflexivity. Defined.

Definition module_hom_comp {R : pzRingType} {U V W : lmodType R}
    (f : module_hom U V) (g : module_hom V W) : module_hom U W.
Proof.
  exists (fun x => g (f x)). intros a x y.
  rewrite (module_hom_linear f) (module_hom_linear g). reflexivity.
Defined.

(** Native MathComp bundled linear maps enter this category without any
    change in their underlying function. *)
Definition module_hom_of_linear {R : pzRingType} {U V : lmodType R}
    (f : {linear U -> V}) : module_hom U V :=
  exist (fun g : U -> V => linear g) (fun x => f x) (linearP f).

Definition module_category (R : pzRingType) : category.
Proof.
  refine {| object := lmodType R;
            hom := @module_hom R;
            identity := @module_hom_id R;
            compose := fun U V W f g => module_hom_comp f g |}.
  - intros U V f. apply module_hom_ext. intro x. reflexivity.
  - intros U V f. apply module_hom_ext. intro x. reflexivity.
  - intros U V W Z f g h. apply module_hom_ext. intro x. reflexivity.
Defined.

Lemma module_hom_of_linear_apply {R : pzRingType} {U V : lmodType R}
    (f : {linear U -> V}) (x : U) : module_hom_of_linear f x = f x.
Proof. reflexivity. Qed.

Lemma module_category_compose_apply {R : pzRingType}
    {U V W : lmodType R} (f : hom (module_category R) U V)
    (g : hom (module_category R) V W) (x : U) :
    module_hom_fun (compose f g) x = module_hom_fun g (module_hom_fun f x).
Proof. reflexivity. Qed.

Definition module_diagram (R : pzRingType) (C : category) :=
  functor C (module_category R).

Definition module_codiagram (R : pzRingType) (C : category) :=
  functor (opposite C) (module_category R).
