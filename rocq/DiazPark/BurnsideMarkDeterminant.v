From mathcomp Require Import all_ssreflect all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Module DiazParkBurnsideMarks.

Section RankMatrices.
Variable R : idomainType.
Variable n : nat.
Variable rank : 'I_n -> nat.
Variable A : 'M[R]_n.
Hypothesis rank_mono : forall i j, A i j != 0 -> (rank i <= rank j)%N.
Hypothesis rank_separates : forall i j, A i j != 0 -> rank i = rank j -> i = j.

Lemma nonzero_permutation_fixed (s : 'S_n) :
  (\prod_i A i (s i)) != 0 -> s = 1%g.
Proof.
move/prodf_neq0=> hnonzero.
have hle : forall i, (rank i <= rank (s i))%N.
  move=> i; exact: rank_mono (hnonzero i isT).
have hsum : (\sum_i rank i = \sum_i rank (s i))%N := reindex_perm s.
have hd : (\sum_i (rank (s i) - rank i) = 0)%N.
  rewrite sumnB // -hsum subnn; by [].
have hz : forall i, (rank (s i) - rank i == 0)%N.
  have h : [forall (i : 'I_n | true), (rank (s i) - rank i == 0)%N].
    by rewrite -sum_nat_eq0 hd eqxx.
  by move=> i; exact: (forall_inP h i isT).
apply/permP=> i; rewrite perm1; symmetry.
apply: (@rank_separates i (s i) (hnonzero i isT)).
apply/eqP; rewrite eqn_leq hle /=.
by move: (hz i); rewrite subn_eq0.
Qed.

Theorem determinant_rank_diagonal : \det A = \prod_i A i i.
Proof.
rewrite /determinant (bigD1 1%g) //= odd_perm1 expr0 mul1r.
have hz : \sum_(s : 'S_n | s != 1%g) (-1) ^+ s * \prod_i A i (s i) = 0.
  apply: big1=> s hs.
  have hp : \prod_i A i (s i) = 0.
    apply/eqP; apply/negPn/negP=> hp.
    by move: hs; rewrite (nonzero_permutation_fixed hp) eqxx.
  by rewrite hp mulr0.
rewrite hz addr0; apply: eq_bigr=> i _; by rewrite perm1.
Qed.

End RankMatrices.

Section Marks.
Variable C : finite_category.
Variable R : idomainType.

Definition burnside_mark_matrix : 'M[R]_#|{: fc_iso_class C}| :=
  \matrix_(i,j) (fc_mark (repr (enum_val i : fc_iso_class C)) (enum_val j : fc_iso_class C))%:R.

Lemma burnside_mark_matrixE i j :
  burnside_mark_matrix i j =
    (#|fc_hom C (repr (enum_val i : fc_iso_class C)) (repr (enum_val j : fc_iso_class C))|)%:R.
Proof. by rewrite /burnside_mark_matrix mxE. Qed.

Variable rank : fc_object C -> nat.
Hypothesis hom_rank : forall x y, fc_hom C x y -> (rank x <= rank y)%N.
Hypothesis equal_rank_iso : forall x y (f : fc_hom C x y), rank x = rank y ->
  exists e : @isomorphism (fc_category C) x y, iso_hom e = f.

Lemma mark_nonzero_hom i j : burnside_mark_matrix i j != 0 ->
  exists f : fc_hom C (repr (enum_val i : fc_iso_class C)) (repr (enum_val j : fc_iso_class C)), True.
Proof.
move=> hn.
have hc : (0 < #|fc_hom C (repr (enum_val i : fc_iso_class C)) (repr (enum_val j : fc_iso_class C))|)%N.
  rewrite lt0n; apply/negP=> /eqP hz.
  by move: hn; rewrite burnside_mark_matrixE hz mulr0n eqxx.
have /card_gt0P[f _] := hc; by exists f.
Qed.

Lemma mark_rank_mono i j : burnside_mark_matrix i j != 0 ->
  (rank (repr (enum_val i : fc_iso_class C)) <= rank (repr (enum_val j : fc_iso_class C)))%N.
Proof. move=> /mark_nonzero_hom[f _]; exact: hom_rank f. Qed.

Lemma mark_rank_separates i j : burnside_mark_matrix i j != 0 ->
  rank (repr (enum_val i : fc_iso_class C)) = rank (repr (enum_val j : fc_iso_class C)) -> i = j.
Proof.
move=> /mark_nonzero_hom[f _] hr.
have [e _] := equal_rank_iso f hr.
have he : fc_class (repr (enum_val i : fc_iso_class C)) = fc_class (repr (enum_val j : fc_iso_class C)).
  apply/fc_class_eq; exact: fc_related_of_iso e.
have ec : enum_val i = enum_val j by move: he; rewrite /fc_class !reprK.
exact: enum_val_inj ec.
Qed.

Theorem burnside_mark_determinant :
  \det burnside_mark_matrix =
    \prod_(i : 'I_#|{: fc_iso_class C}|) (#|fc_hom C (repr (enum_val i : fc_iso_class C)) (repr (enum_val i : fc_iso_class C))|)%:R.
Proof.
rewrite (@determinant_rank_diagonal R #|{: fc_iso_class C}|
  (fun i => rank (repr (enum_val i : fc_iso_class C))) burnside_mark_matrix mark_rank_mono mark_rank_separates).
apply: eq_bigr=> i _; exact: burnside_mark_matrixE.
Qed.

Theorem burnside_mark_determinant_nonzero :
  GRing.pchar R =i pred0 -> \det burnside_mark_matrix != 0.
Proof.
move=> hchar; rewrite burnside_mark_determinant.
apply/prodf_neq0=> i _; rewrite (proj1 (pcharf0P R) hchar) -lt0n.
apply/card_gt0P; exists (fc_identity (repr (enum_val i : fc_iso_class C))); by rewrite inE.
Qed.

End Marks.
End DiazParkBurnsideMarks.
