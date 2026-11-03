(** Actual affine maps determined by arbitrary simplex vertices. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexBasic
  TopologicalSimplexAffine TopologicalSimplexContinuity TopologicalSimplexFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopological DPTopologicalSimplex DPTopologicalSimplexAffine
  DPTopologicalSimplexContinuity DPTopologicalSimplexFunctions.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularSubdivisionAffine.
Section Affine.
Variable Real : realType.

Definition affine_vector {n m} (v : 'I_n.+1 -> simplex Real m)
    (x : simplex Real n) : 'rV[Real]_m.+1 :=
  \row_j weighted_value (fun i => coordinate (v i) j) x.

Lemma affine_vector_coordinate {n m} (v : 'I_n.+1 -> simplex Real m)
    (x : simplex Real n) j :
  affine_vector v x ord0 j = \sum_i coordinate x i * coordinate (v i) j.
Proof. by rewrite /affine_vector mxE. Qed.

Lemma affine_vector_in {n m} (v : 'I_n.+1 -> simplex Real m)
    (x : simplex Real n) : @simplex_set Real m (affine_vector v x).
Proof.
split.
- move=> j; rewrite affine_vector_coordinate; apply sumr_ge0 => i _.
  apply mulr_ge0; exact: coordinate_ge0.
- under eq_bigr do rewrite affine_vector_coordinate.
  rewrite exchange_big.
  under eq_bigr do rewrite -mulr_sumr coordinate_sum mulr1.
  exact: coordinate_sum.
Qed.

Definition affine_simplex {n m} (v : 'I_n.+1 -> simplex Real m)
    (x : simplex Real n) : simplex Real m := simplex_of_vector (affine_vector_in v x).

Lemma affine_simplex_coordinate {n m} (v : 'I_n.+1 -> simplex Real m)
    (x : simplex Real n) j :
  coordinate (affine_simplex v x) j = \sum_i coordinate x i * coordinate (v i) j.
Proof. exact: affine_vector_coordinate. Qed.

Lemma affine_simplex_vertex {n m} (v : 'I_n.+1 -> simplex Real m) i :
  affine_simplex v (vertex Real i) = v i.
Proof.
apply simplex_ext => j; rewrite affine_simplex_coordinate.
change (weighted_value (fun k => coordinate (v k) j) (vertex Real i) = coordinate (v i) j).
exact: weighted_vertex.
Qed.

Lemma affine_vector_continuous {n m} (v : 'I_n.+1 -> simplex Real m) :
  continuous (@affine_vector n m v).
Proof.
apply: (@matrix_continuous_from_coordinates (simplex_space Real n)
  Real 1 m.+1 (@affine_vector n m v)) => i j.
have e : (fun x : simplex Real n => affine_vector v x i j) =
    weighted_value (fun k => coordinate (v k) j).
  by apply functional_extensionality_dep => x; rewrite /affine_vector mxE.
rewrite e; exact: weighted_continuous.
Qed.

Lemma affine_simplex_continuous {n m} (v : 'I_n.+1 -> simplex Real m) :
  continuous (@affine_simplex n m v).
Proof.
apply (@continuous_comp_initial _ _ _ set_val).
exact: affine_vector_continuous.
Qed.

Definition affine_simplex_map {n m} (v : 'I_n.+1 -> simplex Real m) :
    continuousType (simplex_space Real n) (simplex_space Real m) :=
  continuous_map (@affine_simplex_continuous n m v).

Lemma affine_simplex_precompose {n m k} (v : 'I_m.+1 -> simplex Real k)
    (f : 'I_n.+1 -> 'I_m.+1) (x : simplex Real n) :
  affine_simplex v (pushforward f x) = affine_simplex (v \o f) x.
Proof.
apply simplex_ext => j; rewrite !affine_simplex_coordinate.
change (weighted_value (fun i => coordinate (v i) j) (pushforward f x) =
  weighted_value (fun i => coordinate (v (f i)) j) x).
exact: weighted_pushforward.
Qed.

Lemma affine_simplex_pushforward {n m} (f : 'I_n.+1 -> 'I_m.+1)
    (x : simplex Real n) :
  affine_simplex (fun i => vertex Real (f i)) x = pushforward f x.
Proof.
apply simplex_ext => j; rewrite affine_simplex_coordinate pushforward_coordinate.
apply eq_bigr => i _; rewrite coordinate_vertex eq_sym.
by case: (f i == j); rewrite ?mulr1 ?mulr0.
Qed.

Lemma affine_simplex_identity n (x : simplex Real n) :
  affine_simplex (fun i => vertex Real i) x = x.
Proof. rewrite (affine_simplex_pushforward idfun); exact: pushforward_identity. Qed.

Lemma affine_simplex_composition {n m k}
    (v : 'I_n.+1 -> simplex Real m) (w : 'I_m.+1 -> simplex Real k)
    (x : simplex Real n) :
  affine_simplex w (affine_simplex v x) = affine_simplex (fun i => affine_simplex w (v i)) x.
Proof.
apply simplex_ext => j; rewrite !affine_simplex_coordinate.
under eq_bigr do rewrite affine_simplex_coordinate mulr_suml.
rewrite exchange_big; apply eq_bigr => i _.
rewrite affine_simplex_coordinate mulr_sumr.
apply eq_bigr => l _; by rewrite mulrA.
Qed.

End Affine.
End DPSingularSubdivisionAffine.


