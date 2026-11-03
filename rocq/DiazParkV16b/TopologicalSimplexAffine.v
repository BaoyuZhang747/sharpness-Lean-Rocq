From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalSimplexVectors TopologicalSimplexBasic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPTopologicalSimplexAffine.
Import DPTopologicalSimplex DPTopologicalSimplexVectors.
Section Affine.
Variable Real : realType.

Lemma push_vector_nonnegative {n m} (f : 'I_n.+1 -> 'I_m.+1)
    (x : simplex Real n) j : 0 <= push_vector f (simplex_vector x) ord0 j.
Proof.
rewrite push_vector_coordinate; apply: sumr_ge0 => i _.
case: (f i == j); rewrite /= ?mulr1 ?mulr0 //.
exact: coordinate_ge0.
Qed.

Lemma push_vector_total {n m} (f : 'I_n.+1 -> 'I_m.+1)
    (x : 'rV[Real]_n.+1) :
  \sum_j push_vector f x ord0 j = \sum_i x ord0 i.
Proof.
under eq_bigr do rewrite push_vector_coordinate.
rewrite exchange_big; apply: eq_bigr => i _.
rewrite (bigD1 (f i)) // eqxx /= mulr1.
have -> : \sum_(j | j != f i) x ord0 i * (f i == j)%:R = (0 : Real).
  by apply: big1 => j /negbTE hj; rewrite eq_sym hj mulr0.
by rewrite addr0.
Qed.

Lemma push_vector_in {n m} (f : 'I_n.+1 -> 'I_m.+1) (x : simplex Real n) :
  @simplex_set Real m (push_vector f (simplex_vector x)).
Proof.
split; first exact: push_vector_nonnegative.
by rewrite push_vector_total; exact: coordinate_sum.
Qed.

Definition pushforward {n m} (f : 'I_n.+1 -> 'I_m.+1)
    (x : simplex Real n) : simplex Real m := simplex_of_vector (push_vector_in f x).

Lemma pushforward_coordinate {n m} (f : 'I_n.+1 -> 'I_m.+1)
    (x : simplex Real n) j :
  coordinate (pushforward f x) j = \sum_i coordinate x i * (f i == j)%:R.
Proof. exact: push_vector_coordinate. Qed.

Lemma pushforward_identity n (x : simplex Real n) :
  pushforward (@idfun 'I_n.+1) x = x.
Proof. apply: val_inj; exact: push_vector_identity. Qed.

Lemma pushforward_composition {n m k} (f : 'I_n.+1 -> 'I_m.+1)
    (g : 'I_m.+1 -> 'I_k.+1) (x : simplex Real n) :
  pushforward g (pushforward f x) = pushforward (g \o f) x.
Proof. apply: val_inj; exact: push_vector_composition. Qed.

Lemma pushforward_vertex {n m} (f : 'I_n.+1 -> 'I_m.+1) i :
  pushforward f (@vertex Real n i) = vertex Real (f i).
Proof.
apply: simplex_ext => j; rewrite pushforward_coordinate coordinate_vertex.
under eq_bigr do rewrite coordinate_vertex.
rewrite (bigD1 i) // eqxx /= mul1r.
have -> : \sum_(k | k != i) (if k == i then 1 else 0) * (f k == j)%:R = (0 : Real).
  by apply: big1 => k /negbTE ->; rewrite mul0r.
by rewrite addr0 eq_sym; case: (j == f i).
Qed.

End Affine.
End DPTopologicalSimplexAffine.
