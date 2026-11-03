(** Actual last-vertex deletion bijection and signs for outer subdivision faces. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup boolp.
From DiazParkV16b Require Import SubdivisionPermutationSigns SimplexCategoryIdentities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory GroupScope DPSubdivisionPermutationSigns DPSimplexIdentities.
Local Open Scope ring_scope.

Module DPSubdivisionPermutationOuter.
Section Outer.
Variable n : nat.

Definition outer_assemble (i : 'I_n.+1) (q : {perm 'I_n}) := lift_perm ord_max i q.

Lemma outer_remove_exists (p : {perm 'I_n.+1}) (k : 'I_n) :
  exists j : 'I_n, p (lift ord_max k) = lift (p ord_max) j.
Proof.
case: (unliftP (p ord_max) (p (lift ord_max k))) => [j h|h].
- by exists j.
- have e : lift ord_max k = ord_max := perm_inj h.
  have hh := neq_lift ord_max k; by rewrite e eqxx in hh.
Qed.

Definition outer_remove_fun (p : {perm 'I_n.+1}) (k : 'I_n) : 'I_n :=
  proj1_sig (constructive_indefinite_description (outer_remove_exists p k)).

Lemma outer_remove_spec (p : {perm 'I_n.+1}) (k : 'I_n) :
  p (lift ord_max k) = lift (p ord_max) (outer_remove_fun p k).
Proof. exact: (proj2_sig (constructive_indefinite_description (outer_remove_exists p k))). Qed.

Lemma outer_remove_injective (p : {perm 'I_n.+1}) : injective (outer_remove_fun p).
Proof.
move=> x y h; apply: (@lift_inj n.+1 ord_max x y); apply: (@perm_inj _ p).
by rewrite !outer_remove_spec h.
Qed.

Definition outer_remove (p : {perm 'I_n.+1}) : {perm 'I_n} :=
  perm (@outer_remove_injective p).

Lemma outer_remove_apply (p : {perm 'I_n.+1}) k : outer_remove p k = outer_remove_fun p k.
Proof. exact: permE. Qed.

Lemma outer_assemble_last i q : outer_assemble i q ord_max = i.
Proof. exact: lift_perm_id. Qed.

Lemma outer_assemble_lift i q k :
  outer_assemble i q (lift ord_max k) = lift i (q k).
Proof. exact: lift_perm_lift. Qed.

Lemma outer_assemble_remove (p : {perm 'I_n.+1}) :
  outer_assemble (p ord_max) (outer_remove p) = p.
Proof.
apply/permP=> k; case: (unliftP ord_max k) => [j ->|->].
- by rewrite outer_assemble_lift outer_remove_apply -outer_remove_spec.
- exact: outer_assemble_last.
Qed.

Lemma outer_remove_assemble i q : outer_remove (outer_assemble i q) = q.
Proof.
apply/permP=> k; apply: (@lift_inj n.+1 i).
rewrite outer_remove_apply.
have h := outer_remove_spec (outer_assemble i q) k.
by rewrite outer_assemble_last outer_assemble_lift in h.
Qed.

Definition outer_indices (p : {perm 'I_n.+1}) := (p ord_max, outer_remove p).
Definition outer_from_indices (u : 'I_n.+1 * {perm 'I_n}) := outer_assemble u.1 u.2.

Lemma outer_indices_cancel : cancel outer_indices outer_from_indices.
Proof. exact: outer_assemble_remove. Qed.
Lemma outer_from_indices_cancel : cancel outer_from_indices outer_indices.
Proof. by move=> [i q]; rewrite /outer_indices /outer_from_indices /= outer_assemble_last outer_remove_assemble. Qed.

Lemma outer_sign (R : pzRingType) i q :
  permutation_sign R (outer_assemble i q) * (-1 : R)^+n =
  (-1 : R)^+(val i) * permutation_sign R q.
Proof.
rewrite /permutation_sign /outer_assemble odd_lift_perm /=
  -(@signr_odd R n) -(@signr_odd R (val i)).
by case: (odd n); case: (odd (val i)); case: (odd_perm q) => /=;
  rewrite ?expr0 ?expr1 ?mul1r ?mulN1r ?opprK.
Qed.

Theorem outer_reindex (V : zmodType) (F : {perm 'I_n.+1} -> V) :
  \sum_p F p = \sum_i \sum_q F (outer_assemble i q).
Proof.
rewrite pair_bigA.
apply: (reindex outer_from_indices).
apply: onW_bij.
exact: (Bijective outer_from_indices_cancel outer_indices_cancel).
Qed.

Theorem outer_signed_reindex (R : pzRingType) (V : lmodType R)
    (F : {perm 'I_n.+1} -> V) :
  \sum_p (permutation_sign R p * (-1 : R)^+n) *: F p =
    \sum_i \sum_q ((-1 : R)^+(val i) * permutation_sign R q) *:
      F (outer_assemble i q).
Proof.
rewrite outer_reindex; apply eq_bigr => i _; apply eq_bigr => q _.
by rewrite outer_sign.
Qed.
End Outer.
End DPSubdivisionPermutationOuter.
