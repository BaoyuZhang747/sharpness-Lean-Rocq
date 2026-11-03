From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category MackeyStructures.

(** Paired functors before imposing any double-coset formula.  This separates
    the manuscript's inclusion identity from the internally derived all-arrow
    identity.  The coefficient modules need not be finitely generated. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section PairedFunctors.
Variable R : comPzRingType.
Variable C : category.

Record mackey_pair := MackeyPair {
  pair_value : C -> lmodType R;
  pair_pull : forall P Q, hom C P Q ->
    {linear pair_value Q -> pair_value P};
  pair_push : forall P Q, hom C P Q ->
    {linear pair_value P -> pair_value Q};
  pair_pull_id : forall P x, pair_pull (identity P) x = x;
  pair_push_id : forall P x, pair_push (identity P) x = x;
  pair_pull_comp : forall P Q T (f : hom C P Q) (g : hom C Q T) x,
    pair_pull (compose f g) x = pair_pull f (pair_pull g x);
  pair_push_comp : forall P Q T (f : hom C P Q) (g : hom C Q T) x,
    pair_push (compose f g) x = pair_push g (pair_push f x);
  pair_pull_iso : forall P Q (e : isomorphism P Q) x,
    pair_pull (iso_hom e) x = pair_push (iso_inv e) x
}.

Arguments pair_value _ _.
Arguments pair_pull _ {P Q} _.
Arguments pair_push _ {P Q} _.

Variable M : mackey_pair.

Definition pair_mackey_formula (B : mackey_shape C) :=
  forall P Q T (f : hom C P T) (g : hom C Q T) x,
    pair_pull M g (pair_push M f x) =
      \sum_(s : mackey_index B f g)
        pair_push M (span_right (mackey_term B f g s))
          (pair_pull M (span_left (mackey_term B f g s)) x).

Definition mackey_module_of_pair (B : mackey_shape C)
    (h : pair_mackey_formula B) : mackey_module R B :=
  @MackeyModule R C B (pair_value M) (@pair_pull M) (@pair_push M)
    (@pair_pull_id M) (@pair_push_id M) (@pair_pull_comp M)
    (@pair_push_comp M) (@pair_pull_iso M) h.

(** Transport an actual inclusion-style identity along isomorphisms of the
    two source objects.  No Mackey identity is assumed for the transported
    arrows; it follows from the displayed single identity and functor laws. *)
Lemma pair_mackey_iso_transport
    (P Q A B T : C) (e : isomorphism P A) (d : isomorphism Q B)
    (i : hom C A T) (j : hom C B T) (I : finType)
    (s : I -> mackey_span A B)
    (h : forall y, pair_pull M j (pair_push M i y) =
      \sum_(a : I) pair_push M (span_right (s a))
        (pair_pull M (span_left (s a)) y)) x :
    pair_pull M (compose (iso_hom d) j)
      (pair_push M (compose (iso_hom e) i) x) =
      \sum_(a : I)
        pair_push M (compose (span_right (s a)) (iso_inv d))
          (pair_pull M (compose (span_left (s a)) (iso_inv e)) x).
Proof.
rewrite pair_push_comp pair_pull_comp h pair_pull_iso linear_sum.
apply: eq_bigr => a _.
rewrite pair_push_comp pair_pull_comp.
have he := pair_pull_iso (iso_symm e) x.
change (pair_pull M (iso_inv e) x = pair_push M (iso_hom e) x) in he.
by rewrite he.
Qed.

End PairedFunctors.

Definition pair_of_mackey (R : comPzRingType) (C : category)
    (B : mackey_shape C) (M : mackey_module R B) : mackey_pair R C :=
  @MackeyPair R C (mackey_value M) (@mackey_pull R C B M)
    (@mackey_push R C B M) (@mackey_pull_id R C B M)
    (@mackey_push_id R C B M) (@mackey_pull_comp R C B M)
    (@mackey_push_comp R C B M) (@mackey_pull_iso R C B M).
