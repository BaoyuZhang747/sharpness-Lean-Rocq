From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryLimits.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryPushout.

Inductive span_object := span_source | span_left | span_right.
Definition span_hom (x y : span_object) : Prop :=
  match x,y with
  | span_source,_ => True
  | span_left,span_left => True
  | span_right,span_right => True
  | _,_ => False
  end.

Definition span_identity x : span_hom x x.
Proof. destruct x; exact I. Defined.

Definition span_compose x y z : span_hom x y -> span_hom y z -> span_hom x z.
Proof. destruct x,y,z; cbn; intuition. Defined.

Definition span_category : category.
Proof.
  refine (@Build_category span_object span_hom span_identity span_compose _ _ _).
  - intros x y f. apply Prop_irrelevance.
  - intros x y f. apply Prop_irrelevance.
  - intros w x y z f g h. apply Prop_irrelevance.
Defined.

Section Diagram.
Context {C : category} {A B X : C} (i : hom C A B) (j : hom C A X).

Definition span_diagram_object s : C :=
  match s with span_source => A | span_left => B | span_right => X end.

Definition span_diagram_map x y : span_hom x y ->
    hom C (span_diagram_object x) (span_diagram_object y).
Proof.
  destruct x,y; cbn; intro h.
  - exact (identity A).
  - exact i.
  - exact j.
  - contradiction.
  - exact (identity B).
  - contradiction.
  - contradiction.
  - contradiction.
  - exact (identity X).
Defined.

Definition span_diagram : functor span_category C.
Proof.
  refine (@Build_functor span_category C span_diagram_object span_diagram_map _ _).
  - intro x. destruct x; reflexivity.
  - intros x y z f g. destruct x,y,z; cbn in *; try contradiction;
      symmetry; first [apply compose_id_left | apply compose_id_right].
Defined.

End Diagram.

(** This record is the ordinary universal property. Constructors below and in
    the attachment module supply its descent and uniqueness proofs. *)
Record pushout_square {C : category} {A B X Y : C}
    (i : hom C A B) (j : hom C A X) (k : hom C B Y) (l : hom C X Y) := {
  pushout_commutes : compose i k = compose j l;
  pushout_desc : forall Z (a : hom C B Z) (b : hom C X Z),
    compose i a = compose j b -> hom C Y Z;
  pushout_desc_left : forall Z a b w, compose k (@pushout_desc Z a b w) = a;
  pushout_desc_right : forall Z a b w, compose l (@pushout_desc Z a b w) = b;
  pushout_desc_unique : forall Z a b w (d : hom C Y Z),
    compose k d = a -> compose l d = b -> d = @pushout_desc Z a b w
}.

Arguments pushout_commutes {_ _ _ _ _ _ _ _ _} _.
Arguments pushout_desc {_ _ _ _ _ _ _ _ _} _ {_} _ _ _.
Arguments pushout_desc_left {_ _ _ _ _ _ _ _ _} _ {_} _ _ _.
Arguments pushout_desc_right {_ _ _ _ _ _ _ _ _} _ {_} _ _ _.
Arguments pushout_desc_unique {_ _ _ _ _ _ _ _ _} _ {_} _ _ _ _ _ _.

Section Colimit.
Context {C : category} {A B X Y : C}
  {i : hom C A B} {j : hom C A X} {k : hom C B Y} {l : hom C X Y}.
Variable h : pushout_square i j k l.

Definition pushout_cocone : cocone (span_diagram i j) Y.
Proof.
  refine (@Build_cocone span_category C (span_diagram i j) Y
    (fun s => match s with
      | span_source => compose i k | span_left => k | span_right => l end) _).
  intros x y f. destruct x,y; cbn in *; try contradiction;
    try apply compose_id_left; try reflexivity.
  symmetry. exact (pushout_commutes h).
Defined.

Definition pushout_cocone_compat Z (s : cocone (span_diagram i j) Z) :
  compose i (cocone_leg s span_left) = compose j (cocone_leg s span_right).
Proof.
  transitivity (cocone_leg s span_source).
  - exact (@cocone_natural _ _ _ _ s span_source span_left I).
  - symmetry. exact (@cocone_natural _ _ _ _ s span_source span_right I).
Defined.

Definition pushout_colimit : colimiting_cocone (span_diagram i j).
Proof.
  refine (@Build_colimiting_cocone span_category C (span_diagram i j) Y pushout_cocone
    (fun Z s => pushout_desc h (cocone_leg s span_left)
      (cocone_leg s span_right) (pushout_cocone_compat s)) _ _).
  - intros Z s x. destruct x; cbn.
    + rewrite compose_assoc, pushout_desc_left.
      exact (@cocone_natural _ _ _ _ s span_source span_left I).
    + apply pushout_desc_left.
    + apply pushout_desc_right.
  - intros Z s d hd. apply pushout_desc_unique.
    + exact (hd span_left).
    + exact (hd span_right).
Defined.

End Colimit.
End DPCategoryPushout.
