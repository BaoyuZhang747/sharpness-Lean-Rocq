(** Actual fiber computation of right Kan extension. Cartesian lifting gives
    inverse operations on cones, and hence the coefficient-natural limit
    isomorphism. No cofinality or limit comparison is assumed. *)
From mathcomp Require Import boolp.
From DiazPark Require Import Category CategoryLimits CategoryLimitMaps CategoryComma
  CategoryStructured CategoryFibration CategoryFiberLanComma.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FiberPoints.
Context {C D : category} (p : functor C D) (b : D).

Definition fiber_structured_point (x : fiber_category p b) : structured_category p b :=
  structured_point p (fiber_point x) (equality_arrow (eq_sym (fiber_equality x))).

Definition fiber_structured_map {x y : fiber_category p b} (f : hom (fiber_category p b) x y) :
    hom (structured_category p b) (fiber_structured_point x) (fiber_structured_point y).
Proof.
refine (@structured_morphism C D p b (fiber_structured_point x)
  (fiber_structured_point y) (fiber_map f) _).
change (compose (equality_arrow (eq_sym (fiber_equality x))) (fmap p (fiber_map f)) =
  equality_arrow (eq_sym (fiber_equality y))).
transitivity (compose (compose (equality_arrow (eq_sym (fiber_equality x)))
  (compose (fmap p (fiber_map f)) (equality_arrow (fiber_equality y))))
    (equality_arrow (eq_sym (fiber_equality y)))).
- rewrite !compose_assoc, equality_arrow_cancel, compose_id_right. reflexivity.
- rewrite (fiber_over f), equality_arrow_inverse_cancel, compose_id_left. reflexivity.
Defined.
End FiberPoints.
Arguments fiber_structured_point {C D p b} x.
Arguments fiber_structured_map {C D p b x y} f.

Section Cones.
Context {C D E : category} {p : functor C D} (hp : fibration p) (b : D).
Variable M : functor C E.

Definition fiber_ran_lift (X : structured_category p b) :=
  @hp (structured_source X) b (structured_arrow X).

Definition fiber_restrict_cone {v : E}
    (s : cone (functor_comp (structured_projection p b) M) v) :
    cone (functor_comp (fiber_inclusion p b) M) v.
Proof.
refine (@Build_cone (fiber_category p b) E (functor_comp (fiber_inclusion p b) M)
  v (fun x => cone_leg s (fiber_structured_point x)) _).
intros x y f. exact (cone_natural s (fiber_structured_map f)).
Defined.

Lemma fiber_ran_factor_exists (X Y : structured_category p b)
    (f : hom (structured_category p b) X Y) :
    exists k : fiber_hom (lift_fiber_object (fiber_ran_lift X))
      (lift_fiber_object (fiber_ran_lift Y)),
    compose (fiber_map k) (cartesian_arrow (fiber_ran_lift Y)) =
      compose (cartesian_arrow (fiber_ran_lift X)) (structured_map f).
Proof.
assert (ho : fmap p (compose (cartesian_arrow (fiber_ran_lift X)) (structured_map f)) =
  compose (equality_arrow (fiber_equality (lift_fiber_object (fiber_ran_lift X))))
    (structured_arrow Y)).
{ rewrite fmap_compose, cartesian_arrow_over, compose_assoc, (structured_commutes f).
  reflexivity. }
destruct (@cartesian_lift_factor C D p (structured_source Y) b (structured_arrow Y) (fiber_ran_lift Y)
  (lift_fiber_object (fiber_ran_lift X))
  (compose (cartesian_arrow (fiber_ran_lift X)) (structured_map f)) ho) as [k [hk hu]].
exists k. exact hk.
Qed.

Definition fiber_extend_cone {v : E}
    (s : cone (functor_comp (fiber_inclusion p b) M) v) :
    cone (functor_comp (structured_projection p b) M) v.
Proof.
refine (@Build_cone (structured_category p b) E
  (functor_comp (structured_projection p b) M) v
  (fun X => compose (cone_leg s (lift_fiber_object (fiber_ran_lift X)))
    (fmap M (cartesian_arrow (fiber_ran_lift X)))) _).
intros X Y f.
change (compose (compose (cone_leg s (lift_fiber_object (fiber_ran_lift X)))
  (fmap M (cartesian_arrow (fiber_ran_lift X)))) (fmap M (structured_map f)) =
  compose (cone_leg s (lift_fiber_object (fiber_ran_lift Y)))
    (fmap M (cartesian_arrow (fiber_ran_lift Y)))).
destruct (fiber_ran_factor_exists f) as [k hk].
transitivity (compose (cone_leg s (lift_fiber_object (fiber_ran_lift X)))
  (fmap M (compose (cartesian_arrow (fiber_ran_lift X)) (structured_map f)))).
- rewrite compose_assoc. apply f_equal. symmetry.
  exact (fmap_compose M (cartesian_arrow (fiber_ran_lift X)) (structured_map f)).
- rewrite <- hk. transitivity (compose
    (compose (cone_leg s (lift_fiber_object (fiber_ran_lift X))) (fmap M (fiber_map k)))
    (fmap M (cartesian_arrow (fiber_ran_lift Y)))).
  + rewrite compose_assoc. apply f_equal.
    exact (fmap_compose M (fiber_map k) (cartesian_arrow (fiber_ran_lift Y))).
  + exact (f_equal (fun z => compose z (fmap M (cartesian_arrow (fiber_ran_lift Y))))
      (cone_natural s k)).
Defined.

Definition fiber_ran_lift_to_fiber (x : fiber_category p b) :
    fiber_hom (lift_fiber_object (fiber_ran_lift (fiber_structured_point x))) x.
Proof.
refine (@Build_fiber_hom C D p b
  (lift_fiber_object (fiber_ran_lift (fiber_structured_point x))) x
  (cartesian_arrow (fiber_ran_lift (fiber_structured_point x))) _).
change (compose (fmap p (cartesian_arrow (fiber_ran_lift (fiber_structured_point x))))
  (equality_arrow (fiber_equality x)) =
  equality_arrow (cartesian_source_equality (fiber_ran_lift (fiber_structured_point x)))).
rewrite (cartesian_arrow_over (fiber_ran_lift (fiber_structured_point x))).
change (compose (compose (equality_arrow (cartesian_source_equality
  (fiber_ran_lift (fiber_structured_point x))))
  (equality_arrow (eq_sym (fiber_equality x)))) (equality_arrow (fiber_equality x)) =
  equality_arrow (cartesian_source_equality (fiber_ran_lift (fiber_structured_point x)))).
rewrite compose_assoc, equality_arrow_inverse_cancel, compose_id_right. reflexivity.
Defined.

Lemma fiber_restrict_extend_leg {v : E}
    (s : cone (functor_comp (fiber_inclusion p b) M) v) x :
    cone_leg (fiber_restrict_cone (fiber_extend_cone s)) x = cone_leg s x.
Proof. exact (cone_natural s (fiber_ran_lift_to_fiber x)). Qed.

Definition fiber_ran_lift_to_comma (X : structured_category p b) :
    hom (structured_category p b)
      (fiber_structured_point (lift_fiber_object (fiber_ran_lift X))) X.
Proof.
refine (@structured_morphism C D p b
  (fiber_structured_point (lift_fiber_object (fiber_ran_lift X))) X
  (cartesian_arrow (fiber_ran_lift X)) _).
change (compose (equality_arrow (eq_sym (cartesian_source_equality (fiber_ran_lift X))))
  (fmap p (cartesian_arrow (fiber_ran_lift X))) = structured_arrow X).
rewrite cartesian_arrow_over, <- compose_assoc, equality_arrow_inverse_cancel, compose_id_left.
reflexivity.
Defined.

Lemma fiber_extend_restrict_leg {v : E}
    (s : cone (functor_comp (structured_projection p b) M) v) X :
    cone_leg (fiber_extend_cone (fiber_restrict_cone s)) X = cone_leg s X.
Proof. exact (cone_natural s (fiber_ran_lift_to_comma X)). Qed.

Variable K : limiting_cone (functor_comp (structured_projection p b) M).
Variable J : limiting_cone (functor_comp (fiber_inclusion p b) M).

Definition fiber_ran_limit_hom : hom E (limit_object K) (limit_object J) :=
  limit_lift J (fiber_restrict_cone (limit_cone K)).
Definition fiber_ran_limit_inv : hom E (limit_object J) (limit_object K) :=
  limit_lift K (fiber_extend_cone (limit_cone J)).

Lemma fiber_ran_limit_hom_fac x :
    compose fiber_ran_limit_hom (cone_leg (limit_cone J) x) =
      cone_leg (limit_cone K) (fiber_structured_point x).
Proof. exact (limit_lift_fac J (fiber_restrict_cone (limit_cone K)) x). Qed.

Lemma fiber_ran_limit_inv_fac X :
    compose fiber_ran_limit_inv (cone_leg (limit_cone K) X) =
      compose (cone_leg (limit_cone J) (lift_fiber_object (fiber_ran_lift X)))
        (fmap M (cartesian_arrow (fiber_ran_lift X))).
Proof. exact (limit_lift_fac K (fiber_extend_cone (limit_cone J)) X). Qed.

Definition fiber_ran_limit_iso : isomorphism (limit_object K) (limit_object J).
Proof.
refine (@Build_isomorphism E _ _ fiber_ran_limit_hom fiber_ran_limit_inv _ _).
- apply (limit_hom_ext K); intro X.
  rewrite compose_assoc, fiber_ran_limit_inv_fac, <- compose_assoc,
    fiber_ran_limit_hom_fac, compose_id_left.
  exact (fiber_extend_restrict_leg (limit_cone K) X).
- apply (limit_hom_ext J); intro x.
  rewrite compose_assoc, fiber_ran_limit_hom_fac, compose_id_left.
  transitivity (cone_leg (fiber_extend_cone (limit_cone J)) (fiber_structured_point x)).
  + exact (fiber_ran_limit_inv_fac (fiber_structured_point x)).
  + exact (fiber_restrict_extend_leg (limit_cone J) x).
Defined.
End Cones.
Arguments fiber_ran_limit_iso {C D E p} hp b M K J.
Arguments fiber_ran_limit_hom {C D E p} b M K J.
Arguments fiber_ran_limit_hom_fac {C D E p} b M K J x.

Section Naturality.
Context {C D E : category} {p : functor C D} (hp : fibration p) (b : D).
Variables M N : functor C E.
Variable t : nat_trans M N.
Variables KM : limiting_cone (functor_comp (structured_projection p b) M).
Variables KN : limiting_cone (functor_comp (structured_projection p b) N).
Variables JM : limiting_cone (functor_comp (fiber_inclusion p b) M).
Variables JN : limiting_cone (functor_comp (fiber_inclusion p b) N).

Lemma fiber_ran_limit_iso_natural :
    compose (limit_map KM KN (nat_whisker_left (structured_projection p b) t))
      (iso_hom (fiber_ran_limit_iso hp b N KN JN)) =
    compose (iso_hom (fiber_ran_limit_iso hp b M KM JM))
      (limit_map JM JN (nat_whisker_left (fiber_inclusion p b) t)).
Proof.
apply (limit_hom_ext JN); intro x.
change (compose (compose (limit_map KM KN (nat_whisker_left (structured_projection p b) t))
  (fiber_ran_limit_hom b N KN JN)) (cone_leg (limit_cone JN) x) =
  compose (compose (fiber_ran_limit_hom b M KM JM)
    (limit_map JM JN (nat_whisker_left (fiber_inclusion p b) t)))
    (cone_leg (limit_cone JN) x)).
rewrite !compose_assoc, fiber_ran_limit_hom_fac, !limit_map_fac, <- compose_assoc,
  fiber_ran_limit_hom_fac.
exact (limit_map_fac KM KN (nat_whisker_left (structured_projection p b) t)
  (fiber_structured_point x)).
Qed.
End Naturality.
