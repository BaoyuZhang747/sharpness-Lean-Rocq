From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import HomologicalComplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory DiazParkHomological.
Local Open Scope ring_scope.

(** The finite cancellation calculation behind the bar differential.  The
    index of a cochain degree is finite; the coefficient module is arbitrary.
    Category-specific coface maps and their identities are separate data and
    must be constructed before this calculation yields the category bar. *)
Module DiazParkBarAlternating.

Section AlternatingRectangle.
Variable R : pzRingType.
Variable V : lmodType R.

Lemma alternating_rectangle_zero m (F : nat -> nat -> V) :
  (forall i j, (i <= j)%N -> (j < m)%N -> F i j = F j.+1 i) ->
  \sum_(i < m.+1) \sum_(j < m)
    (-1) ^+ i *: ((-1) ^+ j *: F i j) = 0.
Proof.
elim: m F => [|m IH] F h.
- apply: big1 => i _; exact: big_ord0.
- rewrite big_ord_recr /=.
  have hsplit :
      (\sum_(i < m.+1) \sum_(j < m.+1)
        (-1) ^+ i *: ((-1) ^+ j *: F i j)) =
      (\sum_(i < m.+1) \sum_(j < m)
        (-1) ^+ i *: ((-1) ^+ j *: F i j)) +
      (\sum_(i < m.+1) (-1) ^+ i *: ((-1) ^+ m *: F i m)).
    rewrite -big_split; apply: eq_bigr => i _.
    by rewrite big_ord_recr.
  rewrite hsplit.
  have hold :
      \sum_(i < m.+1) \sum_(j < m)
        (-1) ^+ i *: ((-1) ^+ j *: F i j) = 0.
    apply: IH => i j hij hj.
    exact: h i j hij (ltn_trans hj (ltnSn m)).
  rewrite hold add0r -big_split.
  apply: big1 => i _.
  have him : (i <= m)%N by have := ltn_ord i; rewrite ltnS.
  rewrite (h i m him (ltnSn m)) !scalerA -!exprD.
  rewrite addSn [(m + i)%N]addnC exprS mulN1r scaleNr.
  exact: addrN.
Qed.

End AlternatingRectangle.

Section CosimplicialDifferential.
Variable R : pzRingType.
Variable V : nat -> lmodType R.
Variable coface : forall n, nat -> {linear V n -> V n.+1}.

Definition cosimplicial_d n (x : V n) : V n.+1 :=
  \sum_(i < n.+2) (-1) ^+ i *: coface n i x.

Arguments cosimplicial_d _ _ : clear implicits.

Lemma cosimplicial_d_linear n : linear (cosimplicial_d n).
Proof.
move=> a x y; rewrite /cosimplicial_d scaler_sumr -big_split.
apply: eq_bigr => i _.
by rewrite linearP scalerDr !scalerA commr_sign.
Qed.

Arguments cosimplicial_d_linear n : clear implicits.

HB.instance Definition _ n :=
  GRing.isLinear.Build R (V n) (V n.+1) _
    (cosimplicial_d n) (cosimplicial_d_linear n).

Hypothesis coface_identity : forall n i j (x : V n),
  (i <= j)%N -> (j < n.+2)%N ->
  coface n.+1 i (coface n j x) = coface n.+1 j.+1 (coface n i x).

Lemma cosimplicial_d2 n (x : V n) :
  cosimplicial_d n.+1 (cosimplicial_d n x) = 0.
Proof.
rewrite /cosimplicial_d.
transitivity (\sum_(i < n.+3) \sum_(j < n.+2)
  (-1) ^+ i *: ((-1) ^+ j *: coface n.+1 i (coface n j x))).
- apply: eq_bigr => i _; rewrite linear_sum scaler_sumr.
  apply: eq_bigr => j _; by rewrite linearZ.
- apply: (@alternating_rectangle_zero R (V n.+2) n.+2
    (fun i j => coface n.+1 i (coface n j x))) => i j hij hj.
  exact: (@coface_identity n i j x hij hj).
Qed.

Definition cosimplicial_complex : @cochain_complex R :=
  @CochainComplex R V (fun n => (cosimplicial_d n : {linear V n -> V n.+1}))
    cosimplicial_d2.

End CosimplicialDifferential.
End DiazParkBarAlternating.
