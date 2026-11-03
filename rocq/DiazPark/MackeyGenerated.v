From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category ModuleInfrastructure MackeyStructures.

(** Span normal forms and actual generated Mackey subfunctors. The ambient
    category need not be finite for closure and the least-subfunctor property. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section GeneratedMackey.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : @mackey_module R C B.
Variable X : forall Q, mackey_value M Q -> Prop.

Definition normal_generator P (y : mackey_value M P) :=
  exists Q A (a : hom C A Q) (b : hom C A P) (x : mackey_value M Q),
    @X Q x /\ mackey_push M b (mackey_pull M a x) = y.

Definition generated_value P := span_subspace (@normal_generator P).

Lemma generated_contains P x : @X P x -> generated_value P x.
Proof.
move=> hx; apply: span_generator.
exists P, P, (identity P), (identity P), x; split=> //.
by rewrite mackey_pull_id mackey_push_id.
Qed.

Lemma generated_pull P Q (f : hom C P Q) x :
    generated_value Q x -> generated_value P (mackey_pull M f x).
Proof.
apply: (@span_least R (mackey_value M Q) (@normal_generator Q)
  (linear_preimage (mackey_pull M f) (generated_value P))).
move=> y [U [A [a [b [v [hv <-]]]]]].
change (generated_value P (mackey_pull M f (mackey_push M b (mackey_pull M a v)))).
rewrite mackey_formula.
apply: (big_ind (fun z => generated_value P z)); first exact: span_zero.
- move=> z w hz hw; exact: span_add hz hw.
- move=> s _; apply: span_generator.
  exists U, (span_apex (mackey_term B b f s)),
    (compose (span_left (mackey_term B b f s)) a),
    (span_right (mackey_term B b f s)), v; split=> //.
  by rewrite mackey_pull_comp.
Qed.

Lemma generated_push P Q (f : hom C P Q) x :
    generated_value P x -> generated_value Q (mackey_push M f x).
Proof.
apply: (@span_least R (mackey_value M P) (@normal_generator P)
  (linear_preimage (mackey_push M f) (generated_value Q))).
move=> y [U [A [a [b [v [hv <-]]]]]].
apply: span_generator.
exists U, A, a, (compose b f), v; split=> //.
by rewrite mackey_push_comp.
Qed.

Definition generated_mackey : mackey_subfunctor M :=
  @MackeySubfunctor R C B M generated_value (@generated_pull) (@generated_push).

Lemma generated_least (N : mackey_subfunctor M)
    (hX : forall P x, @X P x -> subfunctor_value N P x) P x :
    generated_value P x -> subfunctor_value N P x.
Proof.
apply: (@span_least R (mackey_value M P) (@normal_generator P)
  (subfunctor_value N P)).
move=> y [Q [A [a [b [v [hv <-]]]]]].
apply: subfunctor_push; apply: subfunctor_pull; exact: hX hv.
Qed.

Lemma simple_generated_full (hM : mackey_simple M)
    (hX : exists P, exists x : mackey_value M P, @X P x /\ x <> 0) :
    forall P x, generated_value P x.
Proof.
have [_ hsimple] := hM.
case: (hsimple generated_mackey) => h; last exact h.
have [P [x [hx hn]]] := hX.
exfalso; apply: hn; exact: h (generated_contains hx).
Qed.

End GeneratedMackey.

