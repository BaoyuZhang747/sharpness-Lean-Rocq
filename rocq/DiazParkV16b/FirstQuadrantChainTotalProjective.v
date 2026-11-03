(** Degreewise projectivity of the actual finite-diagonal chain total,
    by its explicit finite sum of coordinate inclusions. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazParkV16b Require Import LinearProjective FirstQuadrantChainBicomplex
  FirstQuadrantChainTotal FirstQuadrantChainTotalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPLinearProjective DPFirstQuadrantChain
  DPFirstQuadrantChainTotal DPFirstQuadrantChainSupport.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainTotalProjective.
Section Projective.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition total_projection p q n (h : (p+q)%coq_nat=n)
    (x : total_term K n) : bicomplex_term K p q := x p q h.
Lemma total_projection_linear p q n (h : (p+q)%coq_nat=n) :
  linear (@total_projection p q n h).
Proof. by move=> r x y. Qed.
HB.instance Definition _ p q n h := GRing.isLinear.Build R _ _ _
  (@total_projection p q n h) (@total_projection_linear p q n h).

Definition diagonal_second n (i : 'I_n.+1) := (n - val i)%coq_nat.
Lemma diagonal_equation n (i : 'I_n.+1) : (val i + diagonal_second i)%coq_nat = n.
Proof.
have hi : (val i < n.+1)%coq_nat := elimT ltP (ltn_ord i).
unfold diagonal_second; lia.
Qed.

Definition diagonal_piece n (i : 'I_n.+1) (a : total_term K n) : total_term K n :=
  total_include (diagonal_equation i) (a (val i) (diagonal_second i) (diagonal_equation i)).

Lemma diagonal_piece_at n (a : total_term K n) p q (h : (p+q)%coq_nat=n)
    (i : 'I_n.+1) :
  @diagonal_piece n i a p q h = if val i == p then a p q h else 0.
Proof.
case: eqP=> [he | he].
- have hq : diagonal_second i = q by unfold diagonal_second; lia.
  unfold diagonal_piece; move: (diagonal_equation i) => hi.
  move: a h; rewrite -he -hq; move=> a h.
  rewrite total_include_same; congr (a _ _ _); apply Prop_irrelevance.
- exact: total_include_other he.
Qed.

Theorem total_diagonal_decomposition n (a : total_term K n) :
  \sum_(i : 'I_n.+1) diagonal_piece i a = a.
Proof.
apply functional_extensionality_dep=> p; apply functional_extensionality_dep=> q;
  apply functional_extensionality_dep=> h.
change (total_projection h (\sum_(i : 'I_n.+1) diagonal_piece i a) = a p q h).
rewrite linear_sum.
have hp : (p < n.+1)%N by apply/ltP; lia.
pose j : 'I_n.+1 := Ordinal hp.
rewrite (bigD1 j) //= /total_projection diagonal_piece_at eqxx.
have hz : \sum_(i : 'I_n.+1 | i != j) @diagonal_piece n i a p q h = 0.
  apply: big1=> i hij; rewrite diagonal_piece_at.
  have hn : val i != p.
    apply/eqP=> hi; have e : i = j by apply val_inj; exact hi.
    by rewrite e eqxx in hij.
  by rewrite (negPf hn).
by rewrite hz addr0.
Qed.

Section Lifts.
Variable n : nat.
Variables M N : lmodType R.
Variable u : {linear M -> N}.
Hypothesis hu : forall y, exists x, u x = y.
Variable a : {linear total_term K n -> N}.
Hypothesis hK : forall p q, linear_projective (bicomplex_term K p q).

Definition diagonal_lift (i : 'I_n.+1) :
    {linear bicomplex_term K (val i) (diagonal_second i) -> M} :=
  proj1_sig (cid (@hK (val i) (diagonal_second i) M N u hu
    (a \o (total_include (diagonal_equation i)) : {linear _ -> _}))).

Lemma diagonal_lift_spec (i : 'I_n.+1) x :
  u (diagonal_lift i x) = a (total_include (diagonal_equation i) x).
Proof.
exact: (proj2_sig (cid (@hK (val i) (diagonal_second i) M N u hu
  (a \o (total_include (diagonal_equation i)) : {linear _ -> _})))) x.
Qed.

Definition total_lift (x : total_term K n) : M :=
  \sum_(i : 'I_n.+1) diagonal_lift i (x (val i) (diagonal_second i) (diagonal_equation i)).

Lemma total_lift_linear : linear total_lift.
Proof.
move=> r x y; rewrite /total_lift scaler_sumr -big_split.
apply: eq_bigr=> i _; exact: linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _ total_lift total_lift_linear.

Lemma total_lift_spec x : u (total_lift x) = a x.
Proof.
rewrite /total_lift linear_sum.
transitivity (\sum_(i : 'I_n.+1) a (diagonal_piece i x)).
- apply: eq_bigr=> i _; exact: diagonal_lift_spec.
- by rewrite -linear_sum total_diagonal_decomposition.
Qed.
End Lifts.

Theorem total_term_projective
    (hK : forall p q, linear_projective (bicomplex_term K p q)) n :
  linear_projective (total_term K n).
Proof.
move=> M N u hu a; exists (total_lift hu a hK : {linear _ -> _}).
exact: total_lift_spec.
Qed.

End Projective.
End DPFirstQuadrantChainTotalProjective.
