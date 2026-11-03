(** Explicit universal constructions used by the slice and fiber arguments.
    The records specify universal properties; existence is only claimed by
    the subsequent proved constructors. No module or finiteness restriction. *)

From DiazPark Require Import Category.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record initial_object (C : category) := {
  initial_point : C;
  initial_arrow : forall x, hom C initial_point x;
  initial_unique : forall x (f : hom C initial_point x), f = initial_arrow x
}.

Arguments initial_point {_} _.
Arguments initial_arrow {_} _ _.
Arguments initial_unique {_} _ {_} _.

Lemma initial_arrow_self {C : category} (i : initial_object C) :
    initial_arrow i (initial_point i) = identity (initial_point i).
Proof. symmetry. apply initial_unique. Qed.

Record terminal_object (C : category) := {
  terminal_point : C;
  terminal_arrow : forall x, hom C x terminal_point;
  terminal_unique : forall x (f : hom C x terminal_point), f = terminal_arrow x
}.

Arguments terminal_point {_} _.
Arguments terminal_arrow {_} _ _.
Arguments terminal_unique {_} _ {_} _.

Lemma terminal_arrow_self {C : category} (t : terminal_object C) :
    terminal_arrow t (terminal_point t) = identity (terminal_point t).
Proof. symmetry. apply terminal_unique. Qed.

Definition terminal_initial_op {C : category} (t : terminal_object C) :
    initial_object (opposite C).
Proof.
  exact (@Build_initial_object (opposite C) (terminal_point t)
    (terminal_arrow t) (fun x f => terminal_unique t f)).
Defined.

Definition initial_terminal_op {C : category} (i : initial_object C) :
    terminal_object (opposite C).
Proof.
  exact (@Build_terminal_object (opposite C) (initial_point i)
    (initial_arrow i) (fun x f => initial_unique i f)).
Defined.

Record cone {C D : category} (F : functor C D) (v : D) := {
  cone_leg : forall x, hom D v (fobj F x);
  cone_natural : forall x y (f : hom C x y),
    compose (cone_leg x) (fmap F f) = cone_leg y
}.

Arguments cone_leg {_ _ _ _} _ _.
Arguments cone_natural {_ _ _ _} _ {_ _} _.

Record limiting_cone {C D : category} (F : functor C D) := {
  limit_object : D;
  limit_cone : cone F limit_object;
  limit_lift : forall v, cone F v -> hom D v limit_object;
  limit_lift_fac : forall v (s : cone F v) x,
    compose (@limit_lift v s) (cone_leg limit_cone x) = cone_leg s x;
  limit_lift_unique : forall v (s : cone F v) (f : hom D v limit_object),
    (forall x, compose f (cone_leg limit_cone x) = cone_leg s x) ->
    f = @limit_lift v s
}.

Arguments limit_object {_ _ _} _.
Arguments limit_cone {_ _ _} _.
Arguments limit_lift {_ _ _} _ {_} _.
Arguments limit_lift_fac {_ _ _} _ {_} _ _.
Arguments limit_lift_unique {_ _ _} _ {_} _ _ _.

Definition initial_cone {C D : category} (F : functor C D)
    (i : initial_object C) : cone F (fobj F (initial_point i)).
Proof.
  refine {| cone_leg := fun x => fmap F (initial_arrow i x) |}.
  intros x y f. rewrite <- fmap_compose.
  rewrite (initial_unique i (compose (initial_arrow i x) f)). reflexivity.
Defined.

(** A limit of an arbitrary diagram on a category with an initial object is
    its value at that object. This is a constructed universal cone. *)
Definition initial_limit {C D : category} (F : functor C D)
    (i : initial_object C) : limiting_cone F.
Proof.
  refine {| limit_object := fobj F (initial_point i);
            limit_cone := initial_cone F i;
            limit_lift := fun v s => cone_leg s (initial_point i) |}.
  - intros v s x. apply cone_natural.
  - intros v s f h. specialize (h (initial_point i)). simpl in h.
    rewrite initial_arrow_self, fmap_id, compose_id_right in h. exact h.
Defined.

(** A contravariant diagram on a category with a terminal object has the
    constructed limit given by evaluation at that terminal object. *)
Definition contravariant_terminal_limit {C D : category}
    (F : functor (opposite C) D) (t : terminal_object C) : limiting_cone F :=
  initial_limit F (terminal_initial_op t).

Record cocone {C D : category} (F : functor C D) (v : D) := {
  cocone_leg : forall x, hom D (fobj F x) v;
  cocone_natural : forall x y (f : hom C x y),
    compose (fmap F f) (cocone_leg y) = cocone_leg x
}.

Arguments cocone_leg {_ _ _ _} _ _.
Arguments cocone_natural {_ _ _ _} _ {_ _} _.

Record colimiting_cocone {C D : category} (F : functor C D) := {
  colimit_object : D;
  colimit_cocone : cocone F colimit_object;
  colimit_desc : forall v, cocone F v -> hom D colimit_object v;
  colimit_desc_fac : forall v (s : cocone F v) x,
    compose (cocone_leg colimit_cocone x) (@colimit_desc v s) = cocone_leg s x;
  colimit_desc_unique : forall v (s : cocone F v) (f : hom D colimit_object v),
    (forall x, compose (cocone_leg colimit_cocone x) f = cocone_leg s x) ->
    f = @colimit_desc v s
}.

Arguments colimit_object {_ _ _} _.
Arguments colimit_cocone {_ _ _} _.
Arguments colimit_desc {_ _ _} _ {_} _.
Arguments colimit_desc_fac {_ _ _} _ {_} _ _.
Arguments colimit_desc_unique {_ _ _} _ {_} _ _ _.

Definition terminal_cocone {C D : category} (F : functor C D)
    (t : terminal_object C) : cocone F (fobj F (terminal_point t)).
Proof.
  refine {| cocone_leg := fun x => fmap F (terminal_arrow t x) |}.
  intros x y f. rewrite <- fmap_compose.
  rewrite (terminal_unique t (compose f (terminal_arrow t y))). reflexivity.
Defined.

(** Dually, a colimit over a category with a terminal object is evaluation
    at that object. *)
Definition terminal_colimit {C D : category} (F : functor C D)
    (t : terminal_object C) : colimiting_cocone F.
Proof.
  refine {| colimit_object := fobj F (terminal_point t);
            colimit_cocone := terminal_cocone F t;
            colimit_desc := fun v s => cocone_leg s (terminal_point t) |}.
  - intros v s x. apply cocone_natural.
  - intros v s f h. specialize (h (terminal_point t)). simpl in h.
    rewrite terminal_arrow_self, fmap_id, compose_id_left in h. exact h.
Defined.
