(** Actual adjacent input transpositions and their unchanged prefix sums. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup.
From DiazParkV16b Require Import SimplexCategoryIdentities SubdivisionPermutationSigns.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory GroupScope DPSimplexIdentities DPSubdivisionPermutationSigns.
Local Open Scope ring_scope.

Module DPSubdivisionPermutationAdjacent.

Lemma transpose_predicate (T : finType) (P : T -> bool) (x y : T)
    (h : P x = P y) z : P (tperm x y z) = P z.
Proof. by case: (tpermP x y z) => [->|->|_ _]; rewrite ?h. Qed.

Section Adjacent.
Variable n : nat.
Variable j : 'I_n.+1.
Definition adjacent_swap := tperm (vertex_widen j) (vertex_successor j).
Definition adjacent_pair (p : {perm 'I_n.+2}) := (adjacent_swap * p)%g.

Lemma adjacent_distinct : vertex_widen j != vertex_successor j.
Proof. by rewrite -val_eqE /= neq_ltn ltnSn. Qed.

Lemma adjacent_pair_apply (p : {perm 'I_n.+2}) k :
  adjacent_pair p k = p (adjacent_swap k).
Proof. exact: permM. Qed.

Lemma adjacent_pair_involutive : involutive adjacent_pair.
Proof. exact: tpermKg. Qed.

Lemma adjacent_pair_sign (R : pzRingType) (p : {perm 'I_n.+2}) :
  permutation_sign R (adjacent_pair p) = - permutation_sign R p.
Proof. apply: permutation_sign_transpose; exact: adjacent_distinct. Qed.

Lemma adjacent_prefix_predicate (c : 'I_n.+2) (hc : c != vertex_widen j) k :
  (adjacent_swap k <= c)%N = (k <= c)%N.
Proof.
apply: (@transpose_predicate [the finType of 'I_n.+2]
  (fun k => (k <= c)%N) (vertex_widen j) (vertex_successor j) _ k).
change ((j <= c)%N = (j < c)%N).
rewrite leq_eqVlt.
have h : (val j == val c) = false.
  apply/negbTE; move: hc; by rewrite eq_sym -val_eqE.
by rewrite h /=.
Qed.

Lemma adjacent_prefix_sum (V : zmodType) (c : 'I_n.+2)
    (hc : c != vertex_widen j) (p : {perm 'I_n.+2}) (F : 'I_n.+2 -> V) :
  \sum_(k : 'I_n.+2 | (k <= c)%N) F (adjacent_pair p k) =
  \sum_(k : 'I_n.+2 | (k <= c)%N) F (p k).
Proof.
rewrite (reindex_inj (can_inj (tpermK (vertex_widen j) (vertex_successor j)))).
under eq_bigl do rewrite adjacent_prefix_predicate //.
by under eq_bigr do rewrite adjacent_pair_apply /adjacent_swap tpermK.
Qed.

Theorem adjacent_invariant_sum_zero (R : pzRingType) (V : lmodType R)
    (F : {perm 'I_n.+2} -> V) (hF : forall p, F (adjacent_pair p) = F p) :
  \sum_p permutation_sign R p *: F p = 0.
Proof. apply: transpose_invariant_sum_zero hF; exact: adjacent_distinct. Qed.
End Adjacent.
End DPSubdivisionPermutationAdjacent.
