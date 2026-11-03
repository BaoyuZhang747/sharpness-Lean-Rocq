(** Actual equality fibers and cartesian lifting, for arbitrary small categories.
    No coherence of chosen lifts or exactness/comma decomposition is assumed. *)
From mathcomp Require Import boolp.
From DiazPark Require Import Category.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition equality_arrow {C : category} {x y : C} (e : x = y) : hom C x y :=
  match e with eq_refl => identity x end.

Lemma equality_arrow_refl {C : category} (x : C) :
  equality_arrow (eq_refl x) = identity x.
Proof. reflexivity. Qed.

Lemma equality_arrow_comp {C : category} {x y z : C} (e : x = y) (f : y = z) :
  compose (equality_arrow e) (equality_arrow f) = equality_arrow (eq_trans e f).
Proof. destruct e, f. apply compose_id_left. Qed.

Lemma equality_arrow_cancel {C : category} {x y : C} (e : x = y) :
  compose (equality_arrow e) (equality_arrow (eq_sym e)) = identity x.
Proof. destruct e. apply compose_id_left. Qed.

Record fiber_object {C D : category} (r : functor C D) (b : D) := {
  fiber_point : C;
  fiber_equality : fobj r fiber_point = b
}.
Arguments fiber_point {_ _ _ _} _.
Arguments fiber_equality {_ _ _ _} _.

Record fiber_hom {C D : category} {r : functor C D} {b : D}
    (x y : fiber_object r b) := {
  fiber_map : hom C (fiber_point x) (fiber_point y);
  fiber_over : compose (fmap r fiber_map) (equality_arrow (fiber_equality y)) =
    equality_arrow (fiber_equality x)
}.
Arguments fiber_map {_ _ _ _ _ _} _.
Arguments fiber_over {_ _ _ _ _ _} _.

Lemma fiber_hom_ext {C D : category} {r : functor C D} {b : D}
    {x y : fiber_object r b} (f g : fiber_hom x y) :
    fiber_map f = fiber_map g -> f = g.
Proof.
  destruct f as [f hf], g as [g hg]. simpl. intro e. destruct e.
  f_equal. apply Prop_irrelevance.
Qed.

Definition fiber_identity {C D : category} {r : functor C D} {b : D}
    (x : fiber_object r b) : fiber_hom x x.
Proof.
  refine {| fiber_map := identity (fiber_point x) |}.
  rewrite fmap_id, compose_id_left. reflexivity.
Defined.

Definition fiber_compose {C D : category} {r : functor C D} {b : D}
    {x y z : fiber_object r b} (f : fiber_hom x y) (g : fiber_hom y z) : fiber_hom x z.
Proof.
  refine {| fiber_map := compose (fiber_map f) (fiber_map g) |}.
  rewrite fmap_compose, compose_assoc, (fiber_over g). apply fiber_over.
Defined.

Definition fiber_category {C D : category} (r : functor C D) (b : D) : category.
Proof.
  refine {| object := fiber_object r b;
            hom := @fiber_hom C D r b;
            identity := @fiber_identity C D r b;
            compose := fun x y z f g => fiber_compose f g |}.
  - intros x y f. apply fiber_hom_ext. apply compose_id_left.
  - intros x y f. apply fiber_hom_ext. apply compose_id_right.
  - intros w x y z f g h. apply fiber_hom_ext. apply compose_assoc.
Defined.

Definition fiber_inclusion {C D : category} (r : functor C D) (b : D) :
    functor (fiber_category r b) C.
Proof.
  refine (@Build_functor (fiber_category r b) C fiber_point
    (fun x y f => fiber_map f) _ _); reflexivity.
Defined.

Definition cartesian {C D : category} (r : functor C D) {a0 a : C}
    (u : hom C a0 a) : Prop :=
  forall (x : C) (h : hom C x a) (beta : hom D (fobj r x) (fobj r a0)),
    compose beta (fmap r u) = fmap r h ->
    exists! k : hom C x a0, fmap r k = beta /\ compose k u = h.

Definition cocartesian {C D : category} (r : functor C D) {a a0 : C}
    (u : hom C a a0) : Prop :=
  forall (x : C) (h : hom C a x) (beta : hom D (fobj r a0) (fobj r x)),
    compose (fmap r u) beta = fmap r h ->
    exists! k : hom C a0 x, fmap r k = beta /\ compose u k = h.

Lemma cocartesian_op_cartesian {C D : category} (r : functor C D)
    {a a0 : C} (u : hom C a a0) :
    cocartesian r u -> cartesian (functor_op r) u.
Proof. exact (fun h => h). Qed.

Record cartesian_lift {C D : category} (r : functor C D)
    (a : C) (b : D) (alpha : hom D b (fobj r a)) := {
  cartesian_source : C;
  cartesian_source_equality : fobj r cartesian_source = b;
  cartesian_arrow : hom C cartesian_source a;
  cartesian_arrow_over : fmap r cartesian_arrow =
    compose (equality_arrow cartesian_source_equality) alpha;
  cartesian_arrow_property : cartesian r cartesian_arrow
}.
Arguments cartesian_lift {C D} r a b alpha.
Arguments cartesian_source {_ _ _ _ _ _} _.
Arguments cartesian_source_equality {_ _ _ _ _ _} _.
Arguments cartesian_arrow {_ _ _ _ _ _} _.
Arguments cartesian_arrow_over {_ _ _ _ _ _} _.
Arguments cartesian_arrow_property {_ _ _ _ _ _} _.

Definition fibration {C D : category} (r : functor C D) : Type :=
  forall (a : C) (b : D) (alpha : hom D b (fobj r a)), cartesian_lift r a b alpha.

Definition lift_fiber_object {C D : category} {r : functor C D}
    {a : C} {b : D} {alpha : hom D b (fobj r a)} (l : cartesian_lift r a b alpha) :
    fiber_object r b :=
  @Build_fiber_object C D r b (cartesian_source l) (cartesian_source_equality l).

Lemma cartesian_lift_factor {C D : category} {r : functor C D}
    {a : C} {b : D} {alpha : hom D b (fobj r a)} (l : cartesian_lift r a b alpha)
    (x : fiber_object r b) (h : hom C (fiber_point x) a) :
    fmap r h = compose (equality_arrow (fiber_equality x)) alpha ->
    exists! k : fiber_hom x (lift_fiber_object l), compose (fiber_map k) (cartesian_arrow l) = h.
Proof.
  intro overh.
  pose (beta := compose (equality_arrow (fiber_equality x))
    (equality_arrow (eq_sym (cartesian_source_equality l)))).
  assert (hb : compose beta (fmap r (cartesian_arrow l)) = fmap r h).
  { rewrite cartesian_arrow_over, overh. unfold beta.
    rewrite compose_assoc, <- (compose_assoc
      (equality_arrow (eq_sym (cartesian_source_equality l)))
      (equality_arrow (cartesian_source_equality l)) alpha).
    rewrite equality_arrow_comp.
    replace (eq_trans (eq_sym (cartesian_source_equality l)) (cartesian_source_equality l))
      with (eq_refl b) by apply Prop_irrelevance.
    rewrite equality_arrow_refl, compose_id_left. reflexivity. }
  destruct (cartesian_arrow_property l (fiber_point x) h beta hb) as [k [[hk he] hu]].
  assert (hkf : compose (fmap r k) (equality_arrow (cartesian_source_equality l)) =
    equality_arrow (fiber_equality x)).
  { rewrite hk. unfold beta. rewrite compose_assoc, equality_arrow_comp.
    replace (eq_trans (eq_sym (cartesian_source_equality l)) (cartesian_source_equality l))
      with (eq_refl b) by apply Prop_irrelevance.
    rewrite equality_arrow_refl, compose_id_right. reflexivity. }
  exists (@Build_fiber_hom C D r b x (lift_fiber_object l) k hkf). split; first exact he.
  intros j hj. apply fiber_hom_ext. apply hu. split; last exact hj.
  unfold beta. pose proof (fiber_over j) as ej.
  simpl in ej.
  rewrite <- ej, compose_assoc, equality_arrow_cancel, compose_id_right. reflexivity.
Qed.

