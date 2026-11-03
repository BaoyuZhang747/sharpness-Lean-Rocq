From mathcomp Require Import all_boot all_algebra generic_quotient.
From DiazPark Require Import Category CategoryFiniteProducts CategoryFinite
  CategoryFiniteClasses BurnsideAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Section Coordinates.
Variable C : finite_category.
Variable R : comPzRingType.
Local Notation I := [the finType of fc_iso_class C].

Definition burnside_column (v : burnside_module C R) : 'cV[R]_#|I| :=
  \matrix_(i,j) v (enum_val i).

Definition burnside_from_column (v : 'cV[R]_#|I|) : burnside_module C R :=
  [ffun a => v (enum_rank a) 0].

Lemma burnside_columnK : cancel burnside_column burnside_from_column.
Proof. move=> v; apply/ffunP=> a; by rewrite ffunE mxE enum_rankK. Qed.

Lemma burnside_from_columnK : cancel burnside_from_column burnside_column.
Proof.
move=> v; apply/matrixP=> i j; rewrite mxE ffunE enum_valK.
by rewrite (ord1 j).
Qed.

Lemma burnside_column_injective : injective burnside_column.
Proof. exact: can_inj burnside_columnK. Qed.

Variable products : forall A B : fc_object C,
  @finite_product_decomposition (fc_category C) A B.

Definition burnside_multiplication_matrix (v : burnside_module C R) :
    'M[R]_#|I| :=
  \matrix_(i,j) (burnside_mul products v (burnside_basis R (enum_val j))) (enum_val i).

Lemma burnside_multiplication_matrixE v i j :
    burnside_multiplication_matrix v i j =
      (burnside_mul products v (burnside_basis R (enum_val j))) (enum_val i).
Proof. by rewrite /burnside_multiplication_matrix mxE. Qed.

Theorem burnside_multiplication_column v w :
    burnside_column (burnside_mul products v w) =
      burnside_multiplication_matrix v *m burnside_column w.
Proof.
apply/matrixP=> i j; rewrite /burnside_column !mxE.
rewrite [in LHS](burnside_basis_expansion w) linear_sum sum_ffunE.
under eq_bigr do rewrite linearZ.
rewrite (big_enum_val (fun a : fc_iso_class C =>
  ((w a) *: burnside_mul products v (burnside_basis R a)) (enum_val i))).
apply: eq_bigr=> k _.
rewrite !ffunE burnside_regular_scale.
by rewrite burnside_multiplication_matrixE mxE mulrC.
Qed.

End Coordinates.

Print Assumptions burnside_columnK.
Print Assumptions burnside_multiplication_column.
