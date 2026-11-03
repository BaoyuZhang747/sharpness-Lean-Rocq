(** Ordinary comma/slice categories. Morphisms satisfy an actual commuting
    triangle, and their category laws are proved from those of the base. *)

From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryLimits.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record costructured_object {C D : category} (F : functor C D) (d : D) := {
  costructured_source : C;
  costructured_arrow : hom D (fobj F costructured_source) d
}.

Arguments costructured_source {_ _ _ _} _.
Arguments costructured_arrow {_ _ _ _} _.

Record costructured_hom {C D : category} {F : functor C D} {d : D}
    (x y : costructured_object F d) := {
  costructured_map : hom C (costructured_source x) (costructured_source y);
  costructured_commutes :
    compose (fmap F costructured_map) (costructured_arrow y) = costructured_arrow x
}.

Arguments costructured_map {_ _ _ _ _ _} _.
Arguments costructured_commutes {_ _ _ _ _ _} _.

Lemma costructured_hom_ext {C D : category} {F : functor C D} {d : D}
    {x y : costructured_object F d} (f g : costructured_hom x y) :
    costructured_map f = costructured_map g -> f = g.
Proof.
  destruct f as [f hf], g as [g hg]. simpl. intro e. destruct e.
  f_equal. apply Prop_irrelevance.
Qed.

Definition costructured_id {C D : category} {F : functor C D} {d : D}
    (x : costructured_object F d) : costructured_hom x x.
Proof.
  refine {| costructured_map := identity (costructured_source x) |}.
  rewrite fmap_id, compose_id_left. reflexivity.
Defined.

Definition costructured_comp {C D : category} {F : functor C D} {d : D}
    {x y z : costructured_object F d}
    (f : costructured_hom x y) (g : costructured_hom y z) : costructured_hom x z.
Proof.
  refine {| costructured_map := compose (costructured_map f) (costructured_map g) |}.
  rewrite fmap_compose, compose_assoc, (costructured_commutes g).
  apply costructured_commutes.
Defined.

Definition costructured_category {C D : category} (F : functor C D) (d : D) : category.
Proof.
  refine {| object := costructured_object F d;
            hom := @costructured_hom C D F d;
            identity := @costructured_id C D F d;
            compose := fun x y z f g => costructured_comp f g |}.
  - intros x y f. apply costructured_hom_ext. apply compose_id_left.
  - intros x y f. apply costructured_hom_ext. apply compose_id_right.
  - intros w x y z f g h. apply costructured_hom_ext. apply compose_assoc.
Defined.

Definition costructured_projection {C D : category} (F : functor C D) (d : D) :
    functor (costructured_category F d) C.
Proof.
  refine (@Build_functor (costructured_category F d) C
    (@costructured_source C D F d) (fun x y f => costructured_map f) _ _);
    reflexivity.
Defined.

Definition over_category (C : category) (p : C) : category :=
  costructured_category (functor_id C) p.

Arguments over_category C p : clear implicits.

Definition over_forget (C : category) (p : C) : functor (over_category C p) C :=
  costructured_projection (functor_id C) p.

Definition over_terminal_object (C : category) (p : C) : over_category C p :=
  @Build_costructured_object C C (functor_id C) p p (identity p).

Arguments over_terminal_object C p : clear implicits.

Definition over_terminal_map (C : category) (p : C) (x : over_category C p) :
    hom (over_category C p) x (over_terminal_object C p).
Proof.
  refine (@Build_costructured_hom C C (functor_id C) p x
    (over_terminal_object C p) (costructured_arrow x) _).
  apply compose_id_right.
Defined.

(** The identity arrow is terminal in the actual slice category. *)
Arguments over_terminal_map C p x : clear implicits.

Definition over_terminal (C : category) (p : C) : terminal_object (over_category C p).
Proof.
  refine {| terminal_point := over_terminal_object C p;
            terminal_arrow := over_terminal_map C p |}.
  intros x f. apply costructured_hom_ext. simpl.
  pose proof (costructured_commutes f) as h. simpl in h.
  rewrite compose_id_right in h. exact h.
Defined.

Definition structured_category {C D : category} (F : functor C D) (d : D) : category :=
  opposite (costructured_category (functor_op F) d).

Definition structured_projection {C D : category} (F : functor C D) (d : D) :
    functor (structured_category F d) C.
Proof.
  refine (@Build_functor (structured_category F d) C
    (fun x => costructured_source x) (fun x y f => costructured_map f) _ _);
    reflexivity.
Defined.
