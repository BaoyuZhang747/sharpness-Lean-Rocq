(** Adjunctions and their actual ordinary-limit comparison.
    An adjunction is specified by unit, counit and both triangle identities.
    Its limit comparison is proved below; it is not an assumed field. *)

From DiazPark Require Import Category CategoryLimits.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record adjunction {C D : category} (L : functor C D) (R : functor D C) := {
  adj_unit : nat_trans (functor_id C) (functor_comp L R);
  adj_counit : nat_trans (functor_comp R L) (functor_id D);
  adj_triangle_left : forall x,
    compose (fmap L (component adj_unit x)) (component adj_counit (fobj L x)) =
      identity (fobj L x);
  adj_triangle_right : forall y,
    compose (component adj_unit (fobj R y)) (fmap R (component adj_counit y)) =
      identity (fobj R y)
}.

Arguments adj_unit {_ _ _ _} _.
Arguments adj_counit {_ _ _ _} _.
Arguments adj_triangle_left {_ _ _ _} _ _.
Arguments adj_triangle_right {_ _ _ _} _ _.

(** Passing to opposite categories reverses an adjunction. The new unit is
    the old counit, and conversely; both naturality laws and both triangles
    are proved directly, without equality of functor records. *)
Definition adjunction_op {C D : category} {L : functor C D} {R : functor D C}
    (a : adjunction L R) : adjunction (functor_op R) (functor_op L).
Proof.
  refine (@Build_adjunction (opposite D) (opposite C)
    (functor_op R) (functor_op L)
    (@Build_nat_trans (opposite D) (opposite D)
      (functor_id (opposite D)) (functor_comp (functor_op R) (functor_op L))
      (fun y => component (adj_counit a) y)
      (fun x y f => eq_sym (naturality (adj_counit a) f)))
    (@Build_nat_trans (opposite C) (opposite C)
      (functor_comp (functor_op L) (functor_op R)) (functor_id (opposite C))
      (fun x => component (adj_unit a) x)
      (fun x y f => eq_sym (naturality (adj_unit a) f))) _ _).
  - intro y. exact (adj_triangle_right a y).
  - intro x. exact (adj_triangle_left a x).
Defined.

Definition cone_restrict {B C D : category} (L : functor B C)
    {F : functor C D} {v : D} (s : cone F v) : cone (functor_comp L F) v.
Proof.
  refine (@Build_cone B D (functor_comp L F) v
    (fun x => cone_leg s (fobj L x)) _).
  intros x y f. exact (cone_natural s (fmap L f)).
Defined.

Arguments cone_restrict {B C D} L {F v} s.

Definition adjunction_cone_extend {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (F : functor D E) {v : E} (s : cone (functor_comp L F) v) : cone F v.
Proof.
  refine {| cone_leg := fun y =>
    compose (cone_leg s (fobj R y)) (fmap F (component (adj_counit a) y)) |}.
  intros x y f.
  change (compose (compose (cone_leg s (fobj R x)) (fmap F (component (adj_counit a) x)))
    (fmap F f) = compose (cone_leg s (fobj R y)) (fmap F (component (adj_counit a) y))).
  cbn [functor_comp functor_id] in *.
  rewrite compose_assoc.
  transitivity (compose (cone_leg s (fobj R x))
    (fmap F (compose (component (adj_counit a) x) f))).
  - apply f_equal. symmetry. exact (fmap_compose F (component (adj_counit a) x) f).
  - transitivity (compose (cone_leg s (fobj R x))
      (fmap F (compose (fmap L (fmap R f)) (component (adj_counit a) y)))).
    + apply f_equal. apply f_equal. symmetry. exact (naturality (adj_counit a) f).
    + transitivity (compose (cone_leg s (fobj R x))
        (compose (fmap F (fmap L (fmap R f))) (fmap F (component (adj_counit a) y)))).
      * apply f_equal. exact (fmap_compose F (fmap L (fmap R f))
          (component (adj_counit a) y)).
      * rewrite <- compose_assoc.
        apply (f_equal (fun k => compose k (fmap F (component (adj_counit a) y)))).
        exact (cone_natural s (fmap R f)).
Defined.

Arguments adjunction_cone_extend {C D E L R} a F {v} s.

Lemma adjunction_cone_extend_restrict {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (F : functor D E) {v : E} (s : cone F v) (y : D) :
    cone_leg (adjunction_cone_extend a F (cone_restrict L s)) y = cone_leg s y.
Proof. exact (cone_natural s (component (adj_counit a) y)). Qed.

Lemma adjunction_cone_restrict_extend {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (F : functor D E) {v : E} (s : cone (functor_comp L F) v) (x : C) :
    cone_leg (adjunction_cone_extend a F s) (fobj L x) = cone_leg s x.
Proof.
  change (compose (cone_leg s (fobj R (fobj L x)))
    (fmap F (component (adj_counit a) (fobj L x))) = cone_leg s x).
  transitivity (compose
    (compose (cone_leg s x) (fmap F (fmap L (component (adj_unit a) x))))
    (fmap F (component (adj_counit a) (fobj L x)))).
  - apply (f_equal (fun k => compose k (fmap F (component (adj_counit a) (fobj L x))))).
    symmetry. exact (cone_natural s (component (adj_unit a) x)).
  - rewrite compose_assoc.
    transitivity (compose (cone_leg s x)
      (fmap F (compose (fmap L (component (adj_unit a) x))
        (component (adj_counit a) (fobj L x))))).
    + apply f_equal. symmetry. exact (fmap_compose F _ _).
    + transitivity (compose (cone_leg s x) (fmap F (identity (fobj L x)))).
      * apply f_equal. apply f_equal. exact (adj_triangle_left a x).
      * transitivity (compose (cone_leg s x) (identity (fobj F (fobj L x)))).
        -- apply f_equal. exact (fmap_id F (fobj L x)).
        -- apply compose_id_right.
Qed.

Arguments adjunction_cone_restrict_extend {C D E L R} a F {v} s x.

(** Restriction along a left adjoint preserves the universal limit. The
    cone on the large category is constructed via the counit. This applies
    to contravariant coefficients along a right adjoint after taking opposites. *)
Definition left_adjoint_limit {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (F : functor D E) (K : limiting_cone (functor_comp L F)) : limiting_cone F.
Proof.
  refine {| limit_object := limit_object K;
            limit_cone := adjunction_cone_extend a F (limit_cone K);
            limit_lift := fun v s => limit_lift K (cone_restrict L s) |}.
  - intros v s y.
    change (compose (limit_lift K (cone_restrict L s))
      (compose (cone_leg (limit_cone K) (fobj R y))
        (fmap F (component (adj_counit a) y))) = cone_leg s y).
    rewrite <- compose_assoc.
    transitivity (compose (cone_leg (cone_restrict L s) (fobj R y))
      (fmap F (component (adj_counit a) y))).
    + apply (f_equal (fun k => compose k (fmap F (component (adj_counit a) y)))).
      exact (limit_lift_fac K (cone_restrict L s) (fobj R y)).
    + exact (cone_natural s (component (adj_counit a) y)).
  - intros v s f h. apply (limit_lift_unique K (cone_restrict L s) f). intro x.
    transitivity (compose f
      (cone_leg (adjunction_cone_extend a F (limit_cone K)) (fobj L x))).
    + apply f_equal. symmetry.
      exact (adjunction_cone_restrict_extend a F (limit_cone K) x).
    + exact (h (fobj L x)).
Defined.

Arguments left_adjoint_limit {C D E L R} a F K.

(** The reverse existence direction: restricting a limiting cone along
    a left adjoint gives a limiting cone, with no extra limit hypothesis. *)
Definition left_adjoint_restrict_limit {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (F : functor D E) (K : limiting_cone F) :
    limiting_cone (functor_comp L F).
Proof.
  refine {| limit_object := limit_object K;
            limit_cone := cone_restrict L (limit_cone K);
            limit_lift := fun v s => limit_lift K (adjunction_cone_extend a F s) |}.
  - intros v s x.
    change (compose (limit_lift K (adjunction_cone_extend a F s))
      (cone_leg (limit_cone K) (fobj L x)) = cone_leg s x).
    rewrite limit_lift_fac.
    exact (adjunction_cone_restrict_extend a F s x).
  - intros v s f h.
    apply (limit_lift_unique K (adjunction_cone_extend a F s) f). intro y.
    change (compose f (cone_leg (limit_cone K) y) =
      compose (cone_leg s (fobj R y)) (fmap F (component (adj_counit a) y))).
    transitivity (compose f (compose (cone_leg (limit_cone K) (fobj L (fobj R y)))
      (fmap F (component (adj_counit a) y)))).
    + apply f_equal. symmetry.
      exact (cone_natural (limit_cone K) (component (adj_counit a) y)).
    + rewrite <- compose_assoc.
      apply (f_equal (fun k => compose k (fmap F (component (adj_counit a) y)))).
      exact (h (fobj R y)).
Defined.

Arguments left_adjoint_restrict_limit {C D E L R} a F K.
