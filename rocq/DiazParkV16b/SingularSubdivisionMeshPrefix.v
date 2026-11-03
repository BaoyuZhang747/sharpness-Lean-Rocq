(** Exact large-ordinal prefix formulas for the actual barycentric cells. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals.
From DiazParkV16b Require Import TopologicalSimplexBasic
  SingularSubdivisionGeometryAffine SingularSubdivisionGeometryBarycenter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import DPTopologicalSimplex DPSingularSubdivisionAffine DPSingularSubdivisionBarycenter.
Local Open Scope ring_scope.

Module DPSingularSubdivisionMeshPrefix.

Lemma prefix_sum_widen (V : zmodType) n (k : 'I_n.+1) (f : 'I_n.+1 -> V) :
  \sum_(i : 'I_(val k).+1) f (widen_ord (ltn_ord k) i) =
    \sum_(i : 'I_n.+1 | (i <= k)%N) f i.
Proof. symmetry; exact: big_ord_narrow_leq. Qed.

Section Prefix.
Variable Real : realType.

Lemma prefix_barycenter_coordinate_filtered n (p : {perm 'I_n.+1}) (k j : 'I_n.+1) :
  coordinate (prefix_barycenter Real p k) j = ((val k).+1%:R)^-1 *
    \sum_(i : 'I_n.+1 | (i <= k)%N) (if j == p i then 1 else 0).
Proof.
rewrite prefix_barycenter_coordinate; congr (_ * _).
exact: prefix_sum_widen.
Qed.

Lemma affine_prefix_barycenter_coordinate n m (v : 'I_n.+1 -> simplex Real m)
    (p : {perm 'I_n.+1}) (k : 'I_n.+1) j :
  coordinate (affine_simplex v (prefix_barycenter Real p k)) j = ((val k).+1%:R)^-1 *
    \sum_(i : 'I_n.+1 | (i <= k)%N) coordinate (v (p i)) j.
Proof.
rewrite /prefix_barycenter affine_simplex_barycenter barycenter_coordinate.
under eq_bigr do rewrite affine_simplex_vertex.
congr (_ * _); exact: prefix_sum_widen.
Qed.

End Prefix.
End DPSingularSubdivisionMeshPrefix.
