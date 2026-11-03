From mathcomp Require Import all_boot all_algebra generic_quotient.
From DiazPark Require Import Category CategoryLimits CategoryFiniteProducts
  CategoryFinite CategoryFiniteClasses BurnsideAlgebra BurnsideCoordinates
  BurnsideMarkDeterminant TraceMarkedMatrices.
Import DiazParkBurnsideMarks GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Section ActualMarkAlgebra.
Variable C : finite_category.
Variable R : idomainType.
Local Notation I := [the finType of fc_iso_class C].

Lemma burnside_mark_column (v : burnside_module C R) i :
    (burnside_mark_matrix C R *m burnside_column v) i 0 =
      burnside_mark (repr (enum_val i : fc_iso_class C)) v.
Proof.
rewrite mxE /burnside_mark.
rewrite (big_enum_val (fun a : fc_iso_class C =>
  v a * (fc_mark (repr (enum_val i : fc_iso_class C)) a)%:R)).
apply: eq_bigr=> j _.
by rewrite burnside_mark_matrixE /burnside_column mxE mulrC.
Qed.

Variable rank : fc_object C -> nat.
Hypothesis hom_rank : forall x y, fc_hom C x y -> (rank x <= rank y)%N.
Hypothesis equal_rank_iso : forall x y (f : fc_hom C x y), rank x = rank y ->
  exists e : @isomorphism (fc_category C) x y, iso_hom e = f.
Hypothesis charzero : GRing.pchar R =i pred0.

Lemma burnside_marks_separate (v w : burnside_module C R) :
    (forall X, burnside_mark X v = burnside_mark X w) -> v = w.
Proof.
move=> h; apply: burnside_column_injective.
apply: trace_mark_matrix_injective.
- exact (@burnside_mark_determinant_nonzero C R rank hom_rank equal_rank_iso charzero).
- apply/matrixP=> i j; rewrite (ord1 j) !burnside_mark_column; exact: h.
Qed.

Variable products : forall A B : fc_object C,
  @finite_product_decomposition (fc_category C) A B.

Theorem burnside_mul_commutative : commutative (burnside_mul (R := R) products).
Proof.
move=> v w; apply: burnside_marks_separate=> X.
by rewrite !burnside_mark_mul mulrC.
Qed.

Theorem burnside_mul_associative : associative (burnside_mul (R := R) products).
Proof.
move=> u v w; apply: burnside_marks_separate=> X.
by rewrite !burnside_mark_mul mulrA.
Qed.

Variable terminal : terminal_object (fc_category C).

Definition burnside_one : burnside_module C R :=
  burnside_basis R (fc_class (terminal_point terminal)).

Lemma burnside_terminal_card X : #|fc_hom C X (terminal_point terminal)| = 1%N.
Proof.
apply/eqP/card1P; exists (terminal_arrow terminal X)=> f.
by rewrite !inE (terminal_unique terminal f) eqxx.
Qed.

Lemma burnside_mark_one X : burnside_mark X burnside_one = 1.
Proof.
by rewrite /burnside_one burnside_mark_basis fc_mark_class burnside_terminal_card.
Qed.

Theorem burnside_one_mul v : burnside_mul products burnside_one v = v.
Proof.
apply: burnside_marks_separate=> X.
by rewrite burnside_mark_mul burnside_mark_one mul1r.
Qed.

Theorem burnside_mul_one v : burnside_mul products v burnside_one = v.
Proof. by rewrite burnside_mul_commutative burnside_one_mul. Qed.

Definition burnside_mark_diagonal (v : burnside_module C R) : 'rV[R]_#|I| :=
  \matrix_(i,j) burnside_mark (repr (enum_val j : fc_iso_class C)) v.

Theorem burnside_mark_intertwining (v : burnside_module C R) :
    burnside_mark_matrix C R *m burnside_multiplication_matrix products v =
      diag_mx (burnside_mark_diagonal v) *m burnside_mark_matrix C R.
Proof.
apply/matrixP=> i j.
rewrite mxE.
have h : \sum_k burnside_mark_matrix C R i k *
    burnside_multiplication_matrix products v k j =
    burnside_mark (repr (enum_val i : fc_iso_class C))
      (burnside_mul products v (burnside_basis R (enum_val j))).
  rewrite -burnside_mark_column mxE.
  apply: eq_bigr=> k _.
  by rewrite burnside_multiplication_matrixE /burnside_column !mxE.
rewrite h burnside_mark_mul burnside_mark_basis.
rewrite mul_diag_mx mxE /burnside_mark_diagonal mxE burnside_mark_matrixE.
reflexivity.
Qed.

Theorem burnside_unit_marks_matrix (v : burnside_module C R) :
    (forall X, burnside_mark X v \is a GRing.unit) ->
      burnside_multiplication_matrix products v \in unitmx.
Proof.
move=> hv; apply: (@trace_unit_marks_unit_matrix R #|I|
  (burnside_mark_matrix C R) (burnside_multiplication_matrix products v)
  (burnside_mark_diagonal v)).
- exact (@burnside_mark_determinant_nonzero C R rank hom_rank equal_rank_iso charzero).
- exact: burnside_mark_intertwining.
- move=> i; rewrite /burnside_mark_diagonal mxE; exact: hv.
Qed.

Definition burnside_unit_marks_inverse (v : burnside_module C R) : burnside_module C R :=
  burnside_from_column
    (invmx (burnside_multiplication_matrix products v) *m burnside_column burnside_one).

Theorem burnside_unit_marks_inverse_right (v : burnside_module C R) :
    (forall X, burnside_mark X v \is a GRing.unit) ->
      burnside_mul products v (burnside_unit_marks_inverse v) = burnside_one.
Proof.
move=> hv; apply: burnside_column_injective.
rewrite burnside_multiplication_column /burnside_unit_marks_inverse burnside_from_columnK.
by rewrite mulmxA mulmxV ?mul1mx //; exact: burnside_unit_marks_matrix hv.
Qed.

Theorem burnside_unit_marks_inverse_left (v : burnside_module C R) :
    (forall X, burnside_mark X v \is a GRing.unit) ->
      burnside_mul products (burnside_unit_marks_inverse v) v = burnside_one.
Proof. move=> hv; rewrite burnside_mul_commutative; exact: burnside_unit_marks_inverse_right hv. Qed.

End ActualMarkAlgebra.

Print Assumptions burnside_marks_separate.
Print Assumptions burnside_mul_associative.
Print Assumptions burnside_unit_marks_inverse_right.
