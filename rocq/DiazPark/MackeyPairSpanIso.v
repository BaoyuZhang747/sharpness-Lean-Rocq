From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category MackeyPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SpanIsomorphism.
Variable R : comPzRingType.
Variable C : category.
Variable M : mackey_pair R C.

Lemma pair_span_iso_invariance (A B P Q : C) (e : isomorphism A B)
    (a : hom C A P) (b : hom C A Q)
    (c : hom C B P) (d : hom C B Q) :
    compose (iso_hom e) c = a -> compose (iso_hom e) d = b ->
    forall x, pair_push M b (pair_pull M a x) = pair_push M d (pair_pull M c x).
Proof.
move=> <- <- x; rewrite pair_pull_comp pair_push_comp pair_pull_iso.
by rewrite -(@pair_push_comp R C M B A B (iso_inv e) (iso_hom e))
  iso_inv_hom pair_push_id.
Qed.

End SpanIsomorphism.
