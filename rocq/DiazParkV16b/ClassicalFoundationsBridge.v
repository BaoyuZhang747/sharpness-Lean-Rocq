(** The logical forms used by the concrete classical real-number libraries
    follow from the already declared MathComp boolp foundation.

    These proofs do NOT replace the axiom constants in precompiled Stdlib
    modules. A theorem using those modules must still report its actual
    Print Assumptions dependencies. This file documents logical strength;
    it supplies no real-number, topological, or cohomological assumption. *)
From mathcomp Require Import boolp.

Set Universe Polymorphism.

Module DPClassicalFoundationsBridge.

Theorem dependent_function_extensionality
    (A : Type) (B : A -> Type) (f g : forall x, B x) :
    (forall x, f x = g x) -> f = g.
Proof.
  exact (@boolp.functional_extensionality_dep A B f g).
Qed.

(** Exact proposition of ClassicalDedekindReals.sig_forall_dec. The stronger
    boolp foundation makes the supplied pointwise decisions unnecessary. *)
Theorem sig_forall_dec_from_boolp (P : nat -> Prop) :
    (forall n, {P n} + {~ P n}) ->
    {n | ~ P n} + {forall n, P n}.
Proof.
  intros pointwise_decision.
  destruct (boolp.pselect (exists n, ~ P n)) as [has_counterexample | no_counterexample].
  - left.
    exact (@boolp.constructive_indefinite_description nat (fun n => ~ P n) has_counterexample).
  - right. intro n.
    destruct (boolp.pselect (P n)) as [holds | fails].
    + exact holds.
    + exfalso. apply no_counterexample. exists n. exact fails.
Qed.

(** Exact proposition of ClassicalDedekindReals.sig_not_dec. *)
Theorem sig_not_dec_from_boolp (P : Prop) : {~ ~ P} + {~ P}.
Proof.
  destruct (boolp.pselect P) as [holds | fails].
  - left. intro not_holds. exact (not_holds holds).
  - right. exact fails.
Qed.

(** Exact proposition of Epsilon.epsilon_statement. The inhabited hypothesis
    is eliminated only while proving existence in Prop; boolp description
    then produces the dependent pair in Type. *)
Theorem epsilon_statement_from_boolp (A : Type) (P : A -> Prop) :
    inhabited A -> {x : A | (exists y, P y) -> P x}.
Proof.
  intro inhabited_A.
  apply (@boolp.constructive_indefinite_description A
    (fun x => (exists y, P y) -> P x)).
  destruct (boolp.pselect (exists y, P y)) as [has_witness | no_witness].
  - destruct has_witness as [x holds]. exists x. intros _. exact holds.
  - destruct inhabited_A as [x]. exists x. intro impossible.
    exfalso. exact (no_witness impossible).
Qed.

End DPClassicalFoundationsBridge.
