(** Actual barycentres of nonempty finite families of simplex points. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology.
From DiazParkV16b Require Import TopologicalSimplexBasic
  SingularSubdivisionGeometryAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import DPTopologicalSimplex DPSingularSubdivisionAffine.
Local Open Scope ring_scope.

Module DPSingularSubdivisionBarycenter.
Section Barycenter.
Variable Real : realType.

Definition uniform_vector n : 'rV[Real]_n.+1 := \row_j (n.+1%:R)^-1.

Lemma uniform_vector_in n : @simplex_set Real n (uniform_vector n).
Proof.
split.
- move=> j; rewrite /uniform_vector mxE invr_ge0; exact: ler0n.
- under eq_bigr do rewrite /uniform_vector mxE.
  rewrite sumr_const card_ord -(mulr_natr ((n.+1%:R : Real)^-1) n.+1).
  by rewrite mulVf // pnatr_eq0.
Qed.

Definition uniform_simplex n : simplex Real n := simplex_of_vector (uniform_vector_in n).

Lemma uniform_simplex_coordinate n j : coordinate (uniform_simplex n) j = (n.+1%:R)^-1.
Proof. by rewrite /coordinate /uniform_simplex /simplex_vector /= /uniform_vector mxE. Qed.

Definition barycenter {n m} (v : 'I_n.+1 -> simplex Real m) : simplex Real m :=
  affine_simplex v (uniform_simplex n).

Lemma barycenter_coordinate {n m} (v : 'I_n.+1 -> simplex Real m) j :
  coordinate (barycenter v) j = (n.+1%:R)^-1 * \sum_i coordinate (v i) j.
Proof.
rewrite /barycenter affine_simplex_coordinate mulr_sumr.
apply eq_bigr => i _; by rewrite uniform_simplex_coordinate.
Qed.

Lemma barycenter_constant n m (x : simplex Real m) :
  barycenter (fun _ : 'I_n.+1 => x) = x.
Proof.
apply simplex_ext => j; rewrite barycenter_coordinate sumr_const card_ord.
rewrite -(mulr_natl (coordinate x j) n.+1) mulrA.
by rewrite mulVf ?mul1r // pnatr_eq0.
Qed.

Lemma affine_simplex_barycenter {n m k} (v : 'I_n.+1 -> simplex Real m)
    (w : 'I_m.+1 -> simplex Real k) :
  affine_simplex w (barycenter v) = barycenter (fun i => affine_simplex w (v i)).
Proof. exact: affine_simplex_composition. Qed.

Definition prefix_barycenter n (p : {perm 'I_n.+1}) (k : 'I_n.+1) : simplex Real n :=
  barycenter (fun i : 'I_(val k).+1 => vertex Real (p (widen_ord (ltn_ord k) i))).

Definition barycentric_cell n (p : {perm 'I_n.+1}) :
    continuousType (simplex_space Real n) (simplex_space Real n) :=
  affine_simplex_map (prefix_barycenter p).

Lemma prefix_barycenter_coordinate n (p : {perm 'I_n.+1}) (k j : 'I_n.+1) :
  coordinate (prefix_barycenter p k) j = ((val k).+1%:R)^-1 *
    \sum_(i : 'I_(val k).+1)
      (if j == p (widen_ord (ltn_ord k) i) then 1 else 0).
Proof.
rewrite /prefix_barycenter barycenter_coordinate.
congr (_ * _); apply eq_bigr => i _; exact: coordinate_vertex.
Qed.

Lemma barycentric_cell_vertex n (p : {perm 'I_n.+1}) k :
  barycentric_cell p (vertex Real k) = prefix_barycenter p k.
Proof. exact: affine_simplex_vertex. Qed.

Lemma barycentric_cell_zero (p : {perm 'I_1}) (x : simplex Real 0) :
  barycentric_cell p x = x.
Proof. exact: simplex_zero_unique. Qed.

End Barycenter.
End DPSingularSubdivisionBarycenter.
