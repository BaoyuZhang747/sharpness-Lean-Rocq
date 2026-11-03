(** A discrete initial family: every object receives exactly one arrow
    from exactly one member. This universal property will be proved from
    the concrete product decompositions in the applications. *)
From DiazPark Require Import Category CategoryLimits.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record initial_family (C : category) := {
  initial_family_index : Type;
  initial_family_object : initial_family_index -> C;
  initial_family_choice : forall x,
    {i : initial_family_index & hom C (initial_family_object i) x};
  initial_family_unique : forall x
    (z : {i : initial_family_index & hom C (initial_family_object i) x}),
    z = initial_family_choice x
}.

Arguments initial_family_index {_} _.
Arguments initial_family_object {_} _ _.
Arguments initial_family_choice {_} _ _.
Arguments initial_family_unique {_} _ {_} _.

Definition initial_family_compose {C : category} (T : initial_family C)
    {x y : C} (f : hom C x y)
    (z : {i : initial_family_index T & hom C (initial_family_object T i) x}) :
    {i : initial_family_index T & hom C (initial_family_object T i) y} :=
  existT _ (projT1 z) (compose (projT2 z) f).

Arguments initial_family_compose {C} T {x y} f z.

Lemma initial_family_choice_natural {C : category} (T : initial_family C)
    {x y : C} (f : hom C x y) :
    initial_family_compose T f (initial_family_choice T x) =
      initial_family_choice T y.
Proof. apply initial_family_unique. Qed.

Lemma initial_family_choice_self {C : category} (T : initial_family C)
    (i : initial_family_index T) :
    initial_family_choice T (initial_family_object T i) =
      existT _ i (identity (initial_family_object T i)).
Proof. symmetry. apply initial_family_unique. Qed.

Definition initial_object_family {C : category} (i : initial_object C) :
    initial_family C.
Proof.
  refine (@Build_initial_family C unit (fun _ => initial_point i)
    (fun x => existT _ tt (initial_arrow i x)) _).
  intros x [j f]. destruct j. rewrite (initial_unique i f). reflexivity.
Defined.
