(** The actual fibre-to-comma adjunction for an arbitrary chosen fibration.
    Cartesian uniqueness proves functoriality, naturality, and both triangles;
    no coherence property of the chosen lifts is assumed. *)
From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryComma CategoryStructured
  CategoryFibration CategoryFiberRan CategoryAdjunction CategoryIsomorphism.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPV28FiberCommaAdjunction.

Definition fiber_comma_functor {C D : category} (p : functor C D) (b : D) :
    functor (fiber_category p b) (structured_category p b).
Proof.
refine (@Build_functor (fiber_category p b) (structured_category p b)
  fiber_structured_point (fun x y f => fiber_structured_map f) _ _).
- intro x. apply costructured_hom_ext. reflexivity.
- intros x y z f g. apply costructured_hom_ext. reflexivity.
Defined.
Arguments fiber_comma_functor {C D} p b.

Lemma fiber_comma_projection {C D : category} (p : functor C D) (b : D) :
    functor_comp (fiber_comma_functor p b) (structured_projection p b) =
      fiber_inclusion p b.
Proof.
apply (@functor_extensionality (fiber_category p b) C
  (functor_comp (fiber_comma_functor p b) (structured_projection p b))
  (fiber_inclusion p b) eq_refl).
reflexivity.
Qed.
Arguments fiber_comma_projection {C D} p b.

Lemma fiber_lift_cancel {C D : category} {p : functor C D} {b : D}
    {a : C} {alpha : hom D b (fobj p a)}
    (l : cartesian_lift p a b alpha) (x : fiber_object p b)
    (f g : fiber_hom x (lift_fiber_object l)) :
    compose (fiber_map f) (cartesian_arrow l) =
      compose (fiber_map g) (cartesian_arrow l) -> f = g.
Proof.
intro eqfg.
assert (ho : fmap p (compose (fiber_map g) (cartesian_arrow l)) =
  compose (equality_arrow (fiber_equality x)) alpha).
{ etransitivity; first exact (fmap_compose p (fiber_map g) (cartesian_arrow l)).
  etransitivity; first exact (f_equal
    (fun u => compose (fmap p (fiber_map g)) u) (cartesian_arrow_over l)).
  etransitivity; first (symmetry; exact (compose_assoc
    (fmap p (fiber_map g)) (equality_arrow (cartesian_source_equality l)) alpha)).
  exact (f_equal (fun u => compose u alpha) (fiber_over g)). }
destruct (@cartesian_lift_factor C D p a b alpha l x
  (compose (fiber_map g) (cartesian_arrow l)) ho) as [k [hk hu]].
transitivity k.
- symmetry. apply hu. exact eqfg.
- apply hu. reflexivity.
Qed.
Arguments fiber_lift_cancel {C D p b a alpha} l x f g _.

Section RightAdjoint.
Context {C D : category} {p : functor C D} (hp : fibration p) (b : D).

Definition fiber_comma_object (X : structured_category p b) : fiber_category p b :=
  lift_fiber_object (fiber_ran_lift hp X).

Definition fiber_comma_map {X Y : structured_category p b}
    (f : hom (structured_category p b) X Y) :
    hom (fiber_category p b) (fiber_comma_object X) (fiber_comma_object Y) :=
  proj1_sig (@constructive_indefinite_description _ _
    (@fiber_ran_factor_exists C D p hp b X Y f)).

Lemma fiber_comma_map_factor {X Y : structured_category p b}
    (f : hom (structured_category p b) X Y) :
    compose (fiber_map (fiber_comma_map f)) (cartesian_arrow (fiber_ran_lift hp Y)) =
      compose (cartesian_arrow (fiber_ran_lift hp X)) (structured_map f).
Proof.
exact (proj2_sig (@constructive_indefinite_description _ _
  (@fiber_ran_factor_exists C D p hp b X Y f))).
Qed.

Lemma fiber_comma_map_identity (X : structured_category p b) :
    fiber_comma_map (identity X) = identity (fiber_comma_object X).
Proof.
apply (fiber_lift_cancel (fiber_ran_lift hp X) _ _ _).
etransitivity; first exact (fiber_comma_map_factor (identity X)).
change (compose (cartesian_arrow (fiber_ran_lift hp X)) (identity (structured_source X)) =
  compose (identity (fiber_point (fiber_comma_object X)))
    (cartesian_arrow (fiber_ran_lift hp X))).
rewrite compose_id_left, compose_id_right. reflexivity.
Qed.

Lemma fiber_comma_map_composition {X Y Z : structured_category p b}
    (f : hom (structured_category p b) X Y) (g : hom (structured_category p b) Y Z) :
    fiber_comma_map (compose f g) = compose (fiber_comma_map f) (fiber_comma_map g).
Proof.
apply (fiber_lift_cancel (fiber_ran_lift hp Z) _ _ _).
etransitivity; first exact (fiber_comma_map_factor (compose f g)).
change (compose (cartesian_arrow (fiber_ran_lift hp X))
  (compose (structured_map f) (structured_map g)) =
  compose (compose (fiber_map (fiber_comma_map f)) (fiber_map (fiber_comma_map g)))
    (cartesian_arrow (fiber_ran_lift hp Z))).
symmetry.
etransitivity; first exact (compose_assoc (fiber_map (fiber_comma_map f))
  (fiber_map (fiber_comma_map g)) (cartesian_arrow (fiber_ran_lift hp Z))).
etransitivity; first exact (f_equal
  (fun u => compose (fiber_map (fiber_comma_map f)) u) (fiber_comma_map_factor g)).
etransitivity; first (symmetry; exact (compose_assoc (fiber_map (fiber_comma_map f))
  (cartesian_arrow (fiber_ran_lift hp Y)) (structured_map g))).
etransitivity; first exact (f_equal (fun u => compose u (structured_map g))
  (fiber_comma_map_factor f)).
exact (compose_assoc (cartesian_arrow (fiber_ran_lift hp X))
  (structured_map f) (structured_map g)).
Qed.

Definition fiber_comma_right_adjoint :
    functor (structured_category p b) (fiber_category p b).
Proof.
refine (@Build_functor (structured_category p b) (fiber_category p b)
  fiber_comma_object (fun X Y f => fiber_comma_map f) _ _).
- exact fiber_comma_map_identity.
- intros X Y Z f g. exact (fiber_comma_map_composition f g).
Defined.

Lemma fiber_comma_unit_exists (x : fiber_category p b) :
    exists k : hom (fiber_category p b) x
      (fiber_comma_object (fiber_structured_point x)),
    compose (fiber_map k)
      (cartesian_arrow (fiber_ran_lift hp (fiber_structured_point x))) =
      identity (fiber_point x).
Proof.
assert (ho : fmap p (identity (fiber_point x)) =
  compose (equality_arrow (fiber_equality x))
    (structured_arrow (fiber_structured_point x))).
{ change (fmap p (identity (fiber_point x)) =
    compose (equality_arrow (fiber_equality x))
      (equality_arrow (eq_sym (fiber_equality x)))).
  rewrite fmap_id, equality_arrow_cancel. reflexivity. }
destruct (@cartesian_lift_factor C D p (fiber_point x) b
  (structured_arrow (fiber_structured_point x))
  (fiber_ran_lift hp (fiber_structured_point x))
  x (identity (fiber_point x)) ho) as [k [hk hu]].
exists k. exact hk.
Qed.

Definition fiber_comma_unit_map (x : fiber_category p b) :
    hom (fiber_category p b) x (fiber_comma_object (fiber_structured_point x)) :=
  proj1_sig (@constructive_indefinite_description _ _ (fiber_comma_unit_exists x)).

Lemma fiber_comma_unit_factor (x : fiber_category p b) :
    compose (fiber_map (fiber_comma_unit_map x))
      (cartesian_arrow (fiber_ran_lift hp (fiber_structured_point x))) =
      identity (fiber_point x).
Proof.
exact (proj2_sig (@constructive_indefinite_description _ _ (fiber_comma_unit_exists x))).
Qed.

Lemma fiber_comma_unit_natural {x y : fiber_category p b}
    (f : hom (fiber_category p b) x y) :
    compose f (fiber_comma_unit_map y) =
      compose (fiber_comma_unit_map x) (fiber_comma_map (fiber_structured_map f)).
Proof.
apply (fiber_lift_cancel (fiber_ran_lift hp (fiber_structured_point y)) _ _ _).
change (compose (compose (fiber_map f) (fiber_map (fiber_comma_unit_map y)))
  (cartesian_arrow (fiber_ran_lift hp (fiber_structured_point y))) =
  compose (compose (fiber_map (fiber_comma_unit_map x))
    (fiber_map (fiber_comma_map (fiber_structured_map f))))
    (cartesian_arrow (fiber_ran_lift hp (fiber_structured_point y)))).
rewrite !compose_assoc, fiber_comma_unit_factor, fiber_comma_map_factor,
  <- compose_assoc, fiber_comma_unit_factor, compose_id_left, compose_id_right.
reflexivity.
Qed.

Definition fiber_comma_unit : nat_trans (functor_id (fiber_category p b))
    (functor_comp (fiber_comma_functor p b) fiber_comma_right_adjoint).
Proof.
refine (@Build_nat_trans (fiber_category p b) (fiber_category p b)
  (functor_id (fiber_category p b))
  (functor_comp (fiber_comma_functor p b) fiber_comma_right_adjoint)
  fiber_comma_unit_map _).
intros x y f. exact (fiber_comma_unit_natural f).
Defined.

Definition fiber_comma_counit :
    nat_trans (functor_comp fiber_comma_right_adjoint (fiber_comma_functor p b))
      (functor_id (structured_category p b)).
Proof.
refine (@Build_nat_trans (structured_category p b) (structured_category p b)
  (functor_comp fiber_comma_right_adjoint (fiber_comma_functor p b))
  (functor_id (structured_category p b))
  (fun X => fiber_ran_lift_to_comma hp X) _).
intros X Y f. apply costructured_hom_ext.
exact (fiber_comma_map_factor f).
Defined.

Lemma fiber_comma_triangle_left (x : fiber_category p b) :
    compose (fmap (fiber_comma_functor p b) (component fiber_comma_unit x))
      (component fiber_comma_counit (fobj (fiber_comma_functor p b) x)) =
      identity (fobj (fiber_comma_functor p b) x).
Proof.
apply costructured_hom_ext. exact (fiber_comma_unit_factor x).
Qed.

Lemma fiber_comma_triangle_right (X : structured_category p b) :
    compose (component fiber_comma_unit (fobj fiber_comma_right_adjoint X))
      (fmap fiber_comma_right_adjoint (component fiber_comma_counit X)) =
      identity (fobj fiber_comma_right_adjoint X).
Proof.
apply (fiber_lift_cancel (fiber_ran_lift hp X) _ _ _).
change (compose (compose (fiber_map (fiber_comma_unit_map (fiber_comma_object X)))
  (fiber_map (fiber_comma_map (fiber_ran_lift_to_comma hp X))))
  (cartesian_arrow (fiber_ran_lift hp X)) =
  compose (identity (fiber_point (fiber_comma_object X)))
    (cartesian_arrow (fiber_ran_lift hp X))).
rewrite compose_assoc, fiber_comma_map_factor, <- compose_assoc,
  fiber_comma_unit_factor. reflexivity.
Qed.

Definition fiber_comma_adjunction :
    adjunction (fiber_comma_functor p b) fiber_comma_right_adjoint :=
  {| adj_unit := fiber_comma_unit;
     adj_counit := fiber_comma_counit;
     adj_triangle_left := fiber_comma_triangle_left;
     adj_triangle_right := fiber_comma_triangle_right |}.

End RightAdjoint.
Arguments fiber_comma_object {C D p} hp b X.
Arguments fiber_comma_right_adjoint {C D p} hp b.
Arguments fiber_comma_unit {C D p} hp b.
Arguments fiber_comma_counit {C D p} hp b.
Arguments fiber_comma_adjunction {C D p} hp b.

End DPV28FiberCommaAdjunction.
