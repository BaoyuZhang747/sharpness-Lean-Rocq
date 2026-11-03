(** Construct the actual adjunction from chosen universal arrows. This is a
    generic algebraic helper; applications must prove the universal property. *)
From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category CategoryAdjunction.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryUniversalReflection.
Section Universal.
Variables C D : category.
Variable R : functor D C.
Variable obj : C -> D.
Variable unit : forall x : C, hom C x (fobj R (obj x)).
Hypothesis universal : forall (x : C) (y : D) (f : hom C x (fobj R y)),
  exists! g : hom D (obj x) y, compose (unit x) (fmap R g) = f.

Definition lift_data (x : C) (y : D) (f : hom C x (fobj R y)) :
    {g : hom D (obj x) y | compose (unit x) (fmap R g) = f}.
Proof. apply cid; destruct (@universal x y f) as [g [hg _]]; by exists g. Defined.
Definition lift (x : C) (y : D) (f : hom C x (fobj R y)) := proj1_sig (lift_data f).
Lemma lift_spec (x : C) (y : D) (f : hom C x (fobj R y)) :
  compose (unit x) (fmap R (lift f)) = f.
Proof. exact (proj2_sig (lift_data f)). Qed.

Lemma universal_cancel (x : C) (y : D) (g h : hom D (obj x) y) :
  compose (unit x) (fmap R g) = compose (unit x) (fmap R h) -> g = h.
Proof.
intro e; destruct (@universal x y (compose (unit x) (fmap R h))) as [k [hk hu]].
rewrite <- (hu g e), <- (hu h (Logic.eq_refl _)); reflexivity.
Qed.

Definition reflection_map (x y : C) (f : hom C x y) : hom D (obj x) (obj y) :=
  lift (compose f (unit y)).

Lemma reflection_map_spec (x y : C) (f : hom C x y) :
  compose (unit x) (fmap R (reflection_map f)) = compose f (unit y).
Proof. exact (lift_spec _). Qed.

Definition reflection : functor C D.
Proof.
refine (@Build_functor C D obj (fun x y f => reflection_map f) _ _).
- intro x; apply universal_cancel.
  rewrite reflection_map_spec fmap_id compose_id_left compose_id_right; reflexivity.
- intros x y z f g; apply universal_cancel.
  rewrite reflection_map_spec fmap_compose -compose_assoc reflection_map_spec.
  rewrite !compose_assoc reflection_map_spec; reflexivity.
Defined.

Definition reflection_unit : nat_trans (functor_id C) (functor_comp reflection R).
Proof.
refine (@Build_nat_trans C C (functor_id C) (functor_comp reflection R) unit _).
intros x y f; symmetry; exact (reflection_map_spec f).
Defined.

Definition counit (y : D) : hom D (obj (fobj R y)) y := lift (identity (fobj R y)).

Lemma counit_spec (y : D) : compose (unit (fobj R y)) (fmap R (counit y)) = identity (fobj R y).
Proof. exact (lift_spec _). Qed.

Definition reflection_counit : nat_trans (functor_comp R reflection) (functor_id D).
Proof.
refine (@Build_nat_trans D D (functor_comp R reflection) (functor_id D) counit _).
intros x y f; apply universal_cancel.
change (compose (unit (fobj R x)) (fmap R (compose (reflection_map (fmap R f)) (counit y))) =
  compose (unit (fobj R x)) (fmap R (compose (counit x) f))).
rewrite !fmap_compose -!compose_assoc reflection_map_spec.
rewrite compose_assoc !counit_spec compose_id_left compose_id_right; reflexivity.
Defined.

Definition reflection_adjunction : adjunction reflection R.
Proof.
refine (@Build_adjunction C D reflection R reflection_unit reflection_counit _ _).
- intro x; apply universal_cancel.
  change (compose (unit x) (fmap R (compose (reflection_map (unit x)) (counit (obj x)))) =
    compose (unit x) (fmap R (identity (obj x)))).
  rewrite fmap_compose -compose_assoc reflection_map_spec compose_assoc counit_spec
    fmap_id !compose_id_right; reflexivity.
- intro y; exact (counit_spec y).
Defined.
End Universal.
End DPCategoryUniversalReflection.
