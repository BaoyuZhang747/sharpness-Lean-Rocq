(** A fibration gives a terminal family in each comma category of a strict
    fiber inclusion. The family and unique factorization are constructed
    from the cartesian lifts, with no decomposition hypothesis. *)
From mathcomp Require Import ssreflect boolp.
From DiazPark Require Import Category CategoryComma CategoryFibration CategoryInitialFamily.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma equality_arrow_inverse_cancel {C : category} {x y : C} (e : x = y) :
    compose (equality_arrow (Logic.eq_sym e)) (equality_arrow e) = identity y.
Proof. destruct e. apply compose_id_left. Qed.

Section FiberComma.
Variables C D : category.
Variable p : functor C D.
Variable hp : fibration p.
Variable b : D.
Variable a : C.

Definition fiber_comma_label (X : costructured_category (fiber_inclusion p b) a) :
    hom D b (fobj p a) :=
  compose (equality_arrow (Logic.eq_sym (fiber_equality (costructured_source X))))
    (fmap p (costructured_arrow X)).

Lemma fiber_comma_label_over (X : costructured_category (fiber_inclusion p b) a) :
    fmap p (costructured_arrow X) =
      compose (equality_arrow (fiber_equality (costructured_source X))) (fiber_comma_label X).
Proof.
unfold fiber_comma_label. rewrite -compose_assoc equality_arrow_cancel compose_id_left.
reflexivity.
Qed.

Definition fiber_comma_terminal (alpha : hom D b (fobj p a)) :
    costructured_category (fiber_inclusion p b) a :=
  @Build_costructured_object (fiber_category p b) C (fiber_inclusion p b) a
    (lift_fiber_object (@hp a b alpha)) (cartesian_arrow (@hp a b alpha)).

Lemma fiber_comma_terminal_label alpha : fiber_comma_label (fiber_comma_terminal alpha) = alpha.
Proof.
unfold fiber_comma_label, fiber_comma_terminal; simpl.
rewrite cartesian_arrow_over -compose_assoc equality_arrow_inverse_cancel compose_id_left.
reflexivity.
Qed.

Lemma fiber_comma_label_map {X Y : costructured_category (fiber_inclusion p b) a}
    (f : hom (costructured_category (fiber_inclusion p b) a) X Y) :
    fiber_comma_label X = fiber_comma_label Y.
Proof.
unfold fiber_comma_label.
rewrite -(costructured_commutes f) fmap_compose.
change (compose (equality_arrow (Logic.eq_sym (fiber_equality (costructured_source X))))
  (compose (fmap p (fiber_map (costructured_map f))) (fmap p (costructured_arrow Y))) =
  compose (equality_arrow (Logic.eq_sym (fiber_equality (costructured_source Y))))
    (fmap p (costructured_arrow Y))).
have h : compose (equality_arrow (Logic.eq_sym (fiber_equality (costructured_source X))))
    (fmap p (fiber_map (costructured_map f))) =
    equality_arrow (Logic.eq_sym (fiber_equality (costructured_source Y))).
  transitivity (compose
    (compose (equality_arrow (Logic.eq_sym (fiber_equality (costructured_source X))))
      (fmap p (fiber_map (costructured_map f))))
    (compose (equality_arrow (fiber_equality (costructured_source Y)))
      (equality_arrow (Logic.eq_sym (fiber_equality (costructured_source Y)))))).
  - rewrite equality_arrow_cancel compose_id_right. reflexivity.
  - rewrite compose_assoc -(compose_assoc (fmap p (fiber_map (costructured_map f)))
      (equality_arrow (fiber_equality (costructured_source Y)))
      (equality_arrow (Logic.eq_sym (fiber_equality (costructured_source Y))))).
    rewrite fiber_over -compose_assoc equality_arrow_inverse_cancel compose_id_left. reflexivity.
rewrite -compose_assoc h. reflexivity.
Qed.

Lemma fiber_comma_factor_exists (X : costructured_category (fiber_inclusion p b) a) :
    exists f : hom (costructured_category (fiber_inclusion p b) a) X
      (fiber_comma_terminal (fiber_comma_label X)), True.
Proof.
destruct (@cartesian_lift_factor C D p a b (fiber_comma_label X) (@hp a b (fiber_comma_label X))
  (costructured_source X) (costructured_arrow X) (fiber_comma_label_over X)) as [k [hk hu]].
exists (@Build_costructured_hom (fiber_category p b) C (fiber_inclusion p b) a X
  (fiber_comma_terminal (fiber_comma_label X)) k hk). exact I.
Qed.

Definition fiber_comma_factor (X : costructured_category (fiber_inclusion p b) a) :=
  proj1_sig (constructive_indefinite_description (fiber_comma_factor_exists X)).

Lemma fiber_comma_factor_unique (X : costructured_category (fiber_inclusion p b) a) alpha
    (f g : hom (costructured_category (fiber_inclusion p b) a) X (fiber_comma_terminal alpha)) : f = g.
Proof.
have hl : fiber_comma_label X = alpha.
  rewrite (fiber_comma_label_map f) fiber_comma_terminal_label. reflexivity.
have ho : fmap p (costructured_arrow X) =
  compose (equality_arrow (fiber_equality (costructured_source X))) alpha.
  rewrite -hl. apply fiber_comma_label_over.
destruct (@cartesian_lift_factor C D p a b alpha (@hp a b alpha) (costructured_source X)
  (costructured_arrow X) ho) as [k [hk hu]].
apply costructured_hom_ext.
transitivity k.
- symmetry; apply hu. exact (costructured_commutes f).
- apply hu. exact (costructured_commutes g).
Qed.

Definition fiber_comma_terminal_family :
    initial_family (opposite (costructured_category (fiber_inclusion p b) a)).
Proof.
refine (@Build_initial_family (opposite (costructured_category (fiber_inclusion p b) a))
  (hom D b (fobj p a)) fiber_comma_terminal
  (fun X => existT _ (fiber_comma_label X) (fiber_comma_factor X)) _).
intros X [alpha f].
have h : alpha = fiber_comma_label X.
  rewrite (fiber_comma_label_map f) fiber_comma_terminal_label. reflexivity.
apply eq_sigT_uncurried. exists h.
apply fiber_comma_factor_unique.
Defined.
End FiberComma.

Arguments fiber_comma_terminal_family {C D p} hp b a.






