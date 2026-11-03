From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Finite vertex pushforward on row vectors. This algebraic construction
    applies to every function of vertex sets, including noninjective ones. *)
Module DPTopologicalSimplexVectors.
Section Pushforward.
Variable R : pzRingType.

Definition push_matrix {n m : nat} (f : 'I_n.+1 -> 'I_m.+1) :
    'M[R]_(n.+1,m.+1) := \matrix_(i,j) (f i == j)%:R.

Definition push_vector {n m : nat} (f : 'I_n.+1 -> 'I_m.+1)
    (x : 'rV[R]_n.+1) : 'rV[R]_m.+1 := x *m push_matrix f.

Lemma push_matrix_identity n : push_matrix (@idfun 'I_n.+1) = 1%:M.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma push_matrix_composition {n m k : nat}
    (f : 'I_n.+1 -> 'I_m.+1) (g : 'I_m.+1 -> 'I_k.+1) :
  push_matrix f *m push_matrix g = push_matrix (g \o f).
Proof.
apply/matrixP => i z; rewrite /push_matrix !mxE.
under eq_bigr do rewrite !mxE.
rewrite (bigD1 (f i)) //= eqxx mul1r.
have -> : \sum_(j | j != f i) (f i == j)%:R * (g j == z)%:R = (0 : R).
  by apply: big1 => j /negbTE hj; rewrite eq_sym hj mul0r.
by rewrite addr0.
Qed.

Lemma push_vector_identity n (x : 'rV[R]_n.+1) :
  push_vector (@idfun 'I_n.+1) x = x.
Proof. by rewrite /push_vector push_matrix_identity mulmx1. Qed.

Lemma push_vector_composition {n m k : nat}
    (f : 'I_n.+1 -> 'I_m.+1) (g : 'I_m.+1 -> 'I_k.+1)
    (x : 'rV[R]_n.+1) :
  push_vector g (push_vector f x) = push_vector (g \o f) x.
Proof. by rewrite /push_vector -mulmxA push_matrix_composition. Qed.

Lemma push_vector_coordinate {n m : nat} (f : 'I_n.+1 -> 'I_m.+1)
    (x : 'rV[R]_n.+1) j :
  push_vector f x ord0 j = \sum_i x ord0 i * (f i == j)%:R.
Proof. by rewrite /push_vector mxE; apply: eq_bigr => i _; rewrite mxE. Qed.

Lemma push_vector_add {n m : nat} (f : 'I_n.+1 -> 'I_m.+1)
    (x y : 'rV[R]_n.+1) :
  push_vector f (x + y) = push_vector f x + push_vector f y.
Proof. exact: mulmxDl. Qed.

Lemma push_vector_scale {n m : nat} (f : 'I_n.+1 -> 'I_m.+1)
    (a : R) (x : 'rV[R]_n.+1) :
  push_vector f (a *: x) = a *: push_vector f x.
Proof. by rewrite /push_vector scalemxAl. Qed.

End Pushforward.
End DPTopologicalSimplexVectors.
