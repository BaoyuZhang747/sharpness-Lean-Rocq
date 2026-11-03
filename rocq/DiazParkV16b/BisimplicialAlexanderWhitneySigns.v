(** Finite alternating-sum cancellation, including the two middle faces. *)
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPAlexanderWhitneySigns.
Section Signs.
Variable R : pzRingType.
Variable V : lmodType R.
Theorem alternating_split p q (a b c : nat -> V)
  (hearly : forall i, (i < p.+1)%N -> a i = b i)
  (hlate : forall j, (j < q.+1)%N -> a (p.+1+j)%N = c j.+1)
  (hmiddle : b p.+1 = c 0%N) :
  (\sum_(i < (p+q).+2) (-1)^+i *: a i) =
  (\sum_(i < p.+2) (-1)^+i *: b i) +
    (-1)^+p *: (\sum_(j < q.+2) (-1)^+j *: c j).
Proof.
have ht : (\sum_(i < (p+q).+2) (-1)^+i *: a i) =
  (\sum_(i < p.+1) (-1)^+i *: b i) +
  (\sum_(j < q.+1) (-1)^+(p.+1+j) *: c (val j).+1).
  have hn : (p+q).+2 = (p.+1+q.+1)%N by rewrite addSn addnS.
  rewrite hn big_split_ord /=; congr (_ + _).
  - apply eq_bigr => i _; by rewrite hearly // ltn_ord.
  - apply eq_bigr => j _; by rewrite hlate // ltn_ord.
have hb : (\sum_(i < p.+2) (-1)^+i *: b i) =
  (\sum_(i < p.+1) (-1)^+i *: b i) + (-1)^+p.+1 *: b p.+1.
  by rewrite big_ord_recr.
have hc : (\sum_(j < q.+2) (-1)^+j *: c j) =
  c 0%N + (\sum_(j < q.+1) (-1)^+(val j).+1 *: c (val j).+1).
  by rewrite big_ord_recl /= expr0 scale1r.
have hl : (\sum_(j < q.+1) (-1)^+(p.+1+j) *: c (val j).+1) =
  (-1)^+p *: (\sum_(j < q.+1) (-1)^+(val j).+1 *: c (val j).+1).
  rewrite scaler_sumr; apply eq_bigr => j _.
  by rewrite scalerA -exprD addSn addnS.
rewrite ht hb hc hl hmiddle exprS mulN1r scaleNr scalerDr.
by rewrite -addrA [(- _ + (_ + _))]addrA addNr add0r.
Qed.
Theorem alternating_split_degree p q n (h : Nat.add p q = n) (a b c : nat -> V)
  (hearly : forall i, (i < p.+1)%N -> a i = b i)
  (hlate : forall j, (j < q.+1)%N -> a (p.+1+j)%N = c j.+1)
  (hmiddle : b p.+1 = c 0%N) :
  (\sum_(i < n.+2) (-1)^+i *: a i) =
  (\sum_(i < p.+2) (-1)^+i *: b i) +
    (-1)^+p *: (\sum_(j < q.+2) (-1)^+j *: c j).
Proof. subst n; exact: alternating_split. Qed.
End Signs.
End DPAlexanderWhitneySigns.
