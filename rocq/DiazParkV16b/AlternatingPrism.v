(** Finite alternating-prism cancellation, with the degree-zero case. *)
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPAlternatingPrism.
Section Sums.
Variable R : pzRingType.
Variable V : lmodType R.

Definition signed k (x : V) := (-1 : R) ^+ k *: x.
Lemma signed_zero x : signed 0 x = x.
Proof. by rewrite /signed expr0 scale1r. Qed.
Lemma signed_successor k x : signed k.+1 x = - signed k x.
Proof. by rewrite /signed exprS mulN1r scaleNr. Qed.
Lemma signed_double_successor i j x : signed (i.+1 + j.+1) x = signed (i + j) x.
Proof. by rewrite addSn addnS !signed_successor opprK. Qed.

Definition rectangle m n (A : nat -> nat -> V) :=
  \sum_(i < m) \sum_(j < n) signed (i + j) (A i j).

Lemma rectangle_corner m n A :
  rectangle m.+1 n.+1 A =
    (\sum_(i < m.+1) signed i (A i 0)) +
    (\sum_(j < n) signed j.+1 (A 0 j.+1)) +
    rectangle m n (fun i j => A i.+1 j.+1).
Proof.
rewrite /rectangle.
transitivity ((\sum_(i < m.+1) signed i (A i 0)) +
  (\sum_(i < m.+1) \sum_(j < n) signed (i + j.+1) (A i j.+1))).
- rewrite -big_split; apply eq_bigr => i _.
  by rewrite big_ord_recl addn0.
- rewrite [in X in _ + X = _]big_ord_recl /=.
  rewrite addrA; congr (_ + _).
  apply eq_bigr => i _; apply eq_bigr => j _.
  exact: signed_double_successor.
Qed.

Lemma cancel_corners (a b c d r s : V) :
  ((a - c) + (- b - d) + r) + (c + d + s) = a - b + (r + s).
Proof.
rewrite (addrACA a (-c) (-b) (-d)) -opprD.
by rewrite (addrAC (a-b) (-(c+d)) r) addrA subrK -addrA.
Qed.

Theorem alternating_prism n (A B : nat -> nat -> V) :
  (forall i j, (i <= n)%N -> (j < i)%N -> A i j = B i.-1 j) ->
  (forall i j, (i <= n)%N -> (j <= n.+1)%N -> (i.+1 < j)%N ->
    A i j = B i j.-1) ->
  (forall i, (i < n)%N -> A i i.+1 = A i.+1 i.+1) ->
  rectangle n.+1 n.+2 A + rectangle n n.+1 B = A 0 0 - A n n.+1.
Proof.
elim: n A B => [|n IH] A B hleft hright hmid.
- rewrite /rectangle !big_ord_recl !big_ord0 /= !addr0.
  by rewrite signed_zero signed_successor signed_zero.
- have hcol : (\sum_(i < n.+2) signed i (A i 0)) =
      A 0 0 - \sum_(i < n.+1) signed i (B i 0).
    rewrite big_ord_recl /= signed_zero -sumrN; congr (_ + _).
    apply eq_bigr => i _; rewrite signed_successor.
    congr (- signed i _); apply hleft; first exact: ltn_ord i.
    exact: ltn0Sn.
  have hrow : (\sum_(j < n.+2) signed j.+1 (A 0 j.+1)) =
      - A 0 1 - \sum_(j < n.+1) signed j.+1 (B 0 j.+1).
    rewrite big_ord_recl /= signed_successor signed_zero -sumrN.
    congr (_ + _); apply eq_bigr => j _.
    rewrite !signed_successor !opprK.
    congr (signed j _); apply hright.
    + exact: leq0n.
    + exact: ltn_ord j.
    + exact: ltn0Sn.
  have hshift := IH (fun i j => A i.+1 j.+1) (fun i j => B i.+1 j.+1).
  have hs : rectangle n.+1 n.+2 (fun i j => A i.+1 j.+1) +
      rectangle n n.+1 (fun i j => B i.+1 j.+1) =
      A 1 1 - A n.+1 n.+2.
    apply hshift.
    + move=> i j hi hj; rewrite hleft //.
      by rewrite prednK // (leq_ltn_trans (leq0n j) hj).
    + move=> i j hi hj hij; rewrite hright //.
      by rewrite prednK // (leq_ltn_trans (leq0n i.+1) hij).
    + move=> i hi; apply hmid; exact hi.
  rewrite (@rectangle_corner n.+1 n.+2 A) (@rectangle_corner n n.+1 B)
    hcol hrow cancel_corners hs.
  rewrite (hmid 0 (ltn0Sn n)).
  by rewrite subrKA.
Qed.
End Sums.
End DPAlternatingPrism.
