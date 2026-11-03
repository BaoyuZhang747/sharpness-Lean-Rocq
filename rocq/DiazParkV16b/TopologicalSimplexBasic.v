From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalCategory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** The usual closed affine simplex, with its actual subset topology.
    The real field here is independent of any homological coefficient ring. *)
Module DPTopologicalSimplex.
Section Simplex.
Variable Real : realType.

Definition simplex_set (n : nat) : set 'rV[Real]_n.+1 :=
  [set x | (forall i, 0 <= x ord0 i) /\ \sum_i x ord0 i = 1].
Arguments simplex_set n : clear implicits.

Definition simplex (n : nat) := set_type (simplex_set n).

Definition simplex_space (n : nat) : topologicalType :=
  [the topologicalType of set_type (simplex_set n)].

Definition simplex_vector {n} (x : simplex n) : 'rV[Real]_n.+1 := val x.

Definition coordinate {n} (x : simplex n) (i : 'I_n.+1) : Real :=
  simplex_vector x ord0 i.

Lemma coordinate_ge0 {n} (x : simplex n) i : 0 <= coordinate x i.
Proof. exact: (proj1 (set_valP x) i). Qed.

Lemma coordinate_sum {n} (x : simplex n) : \sum_i coordinate x i = 1.
Proof. exact: (proj2 (set_valP x)). Qed.

Lemma simplex_ext {n} (x y : simplex n) :
  (forall i, coordinate x i = coordinate y i) -> x = y.
Proof.
move=> h; apply: val_inj; apply/matrixP => i j.
by have -> : i = ord0 := ord1 i; exact: h.
Qed.

Definition simplex_of_vector {n} (x : 'rV[Real]_n.+1)
    (hx : simplex_set n x) : simplex n :=
  exist _ x (mem_set hx).

Lemma simplex_of_vector_at {n} (x : 'rV[Real]_n.+1)
    (hx : simplex_set n x) i : coordinate (simplex_of_vector hx) i = x ord0 i.
Proof. reflexivity. Qed.

Definition vertex_vector {n} (i : 'I_n.+1) : 'rV[Real]_n.+1 :=
  \row_j (if j == i then 1 else 0).

Lemma vertex_vector_in {n} (i : 'I_n.+1) : simplex_set n (vertex_vector i).
Proof.
split.
- move=> j; rewrite /vertex_vector mxE; by case: ifP.
- under eq_bigr do rewrite /vertex_vector mxE.
  rewrite (bigD1 i) // eqxx.
  have -> : \sum_(j | j != i) (if j == i then 1 else 0) = (0 : Real).
    by apply: big1 => j /negbTE ->.
  by rewrite /= addr0.
Qed.

Definition vertex {n} (i : 'I_n.+1) : simplex n :=
  simplex_of_vector (vertex_vector_in i).

Lemma coordinate_vertex {n} (i j : 'I_n.+1) :
  coordinate (vertex i) j = (if j == i then 1 else 0).
Proof. by rewrite /coordinate /vertex /simplex_vector /= /vertex_vector mxE. Qed.

Lemma coordinate_zero_dimension (x : simplex 0) : coordinate x ord0 = 1.
Proof. by have := coordinate_sum x; rewrite big_ord1. Qed.

Lemma simplex_zero_unique (x y : simplex 0) : x = y.
Proof.
apply: simplex_ext => i; have -> : i = ord0 := ord1 i.
by rewrite !coordinate_zero_dimension.
Qed.

Definition boundary_set n : set (simplex n) :=
  [set x | exists i, coordinate x i = 0].
Arguments boundary_set n : clear implicits.

Definition boundary n := set_type (boundary_set n).

Definition boundary_space n : topologicalType :=
  [the topologicalType of set_type (boundary_set n)].

Lemma boundary_zero_empty : boundary_set 0 = set0.
Proof.
apply/seteqP; split => x.
- move=> [i hi]; have hi0 : i = ord0 := ord1 i.
  by move: hi; rewrite hi0 coordinate_zero_dimension => /eqP; rewrite oner_eq0.
- by [].
Qed.

End Simplex.
End DPTopologicalSimplex.
