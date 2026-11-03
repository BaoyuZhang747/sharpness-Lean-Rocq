From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category MackeyStructures.

(** Uniform composition formula for restriction-then-transfer normal forms.
    The resulting finite family is independent of the coefficient vector. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section NormalForms.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : @mackey_module R C B.

Definition span_action P Q (s : @mackey_span C P Q) (x : mackey_value M P) :=
  mackey_push M (span_right s) (mackey_pull M (span_left s) x).

Definition composite_span P Q T (s : @mackey_span C P Q) (t : @mackey_span C Q T)
    (i : mackey_index B (span_right s) (span_left t)) : @mackey_span C P T :=
  @MackeySpan C P T (span_apex (mackey_term B (span_right s) (span_left t) i))
    (compose (span_left (mackey_term B (span_right s) (span_left t) i)) (span_left s))
    (compose (span_right (mackey_term B (span_right s) (span_left t) i)) (span_right t)).

Lemma span_action_compose P Q T (s : @mackey_span C P Q) (t : @mackey_span C Q T) x :
    span_action t (span_action s x) =
      \sum_(i : mackey_index B (span_right s) (span_left t))
        span_action (@composite_span P Q T s t i) x.
Proof.
rewrite /span_action mackey_formula linear_sum.
apply: eq_bigr => i _.
by rewrite /composite_span /= mackey_pull_comp mackey_push_comp.
Qed.

Lemma pull_is_span P Q (f : hom C P Q) x :
    mackey_pull M f x = span_action (@MackeySpan C Q P P f (identity P)) x.
Proof. by rewrite /span_action /= mackey_push_id. Qed.

Lemma push_is_span P Q (f : hom C P Q) x :
    mackey_push M f x = span_action (@MackeySpan C P Q P (identity P) f) x.
Proof. by rewrite /span_action /= mackey_pull_id. Qed.

Lemma span_action_sum P Q (s : @mackey_span C P Q) (I : Type)
    (r : seq I) (v : I -> mackey_value M P) :
    span_action s (\sum_(i <- r) v i) = \sum_(i <- r) span_action s (v i).
Proof. by rewrite /span_action !linear_sum. Qed.

Definition has_span_normal_form P Q (f : mackey_value M P -> mackey_value M Q) :=
  exists ss : seq (@mackey_span C P Q),
    forall x, f x = \sum_(s <- ss) span_action s x.

Lemma normal_form_compose P Q T (f : mackey_value M P -> mackey_value M Q)
    (g : mackey_value M Q -> mackey_value M T) :
    has_span_normal_form f -> has_span_normal_form g ->
    has_span_normal_form (fun x => g (f x)).
Proof.
move=> [ss hf] [ts hg].
exists (flatten [seq flatten [seq
  [seq @composite_span P Q T s t i |
      i <- enum (mackey_index B (span_right s) (span_left t))] | s <- ss] | t <- ts]).
move=> x; rewrite hg hf big_flatten big_map.
apply: eq_bigr => t _; rewrite span_action_sum big_flatten big_map.
apply: eq_bigr => s _; rewrite span_action_compose big_map.
by rewrite big_enum.
Qed.

(** This inductive predicate is the literal finite-composite closure of the
    ordinary structure maps; it contains no normalization hypothesis. *)
Inductive structure_composite : forall P Q,
    (mackey_value M P -> mackey_value M Q) -> Prop :=
| structure_identity P : @structure_composite P P (fun x => x)
| structure_pull P Q (f : hom C P Q) : @structure_composite Q P (mackey_pull M f)
| structure_push P Q (f : hom C P Q) : @structure_composite P Q (mackey_push M f)
| structure_compose P Q T f g of @structure_composite P Q f & @structure_composite Q T g :
    @structure_composite P T (fun x => g (f x)).

Theorem every_structure_composite_normalizes P Q f :
    @structure_composite P Q f -> has_span_normal_form f.
Proof.
move=> hword; elim: hword => [U|U V a|U V a|U V W g h hg ihg hh ihh].
- exists [:: @MackeySpan C U U U (identity U) (identity U)] => x.
  by rewrite big_cons big_nil addr0 /span_action /= mackey_pull_id mackey_push_id.
- exists [:: @MackeySpan C V U U a (identity U)] => x.
  rewrite big_cons big_nil addr0; exact: pull_is_span.
- exists [:: @MackeySpan C U V U (identity U) a] => x.
  rewrite big_cons big_nil addr0; exact: push_is_span.
- exact: normal_form_compose ihg ihh.
Qed.

End NormalForms.


