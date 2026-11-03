(** The actual barycentric cells shrink affine vertex mesh by n/(n+1). *)
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalSimplexBasic
  SingularSubdivisionGeometryAffine SingularSubdivisionGeometryBarycenter
  SingularSubdivisionMeshAffine SingularSubdivisionMeshAverages
  SingularSubdivisionMeshFactor SingularSubdivisionMeshPrefix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopologicalSimplex DPSingularSubdivisionAffine DPSingularSubdivisionBarycenter
  DPSingularSubdivisionMeshAffine DPSingularSubdivisionMeshAverages
  DPSingularSubdivisionMeshFactor DPSingularSubdivisionMeshPrefix.
Local Open Scope ring_scope.

Module DPSingularSubdivisionMeshCells.

Definition prefix_set n (k : 'I_n.+1) : {set 'I_n.+1} := [set i : 'I_n.+1 | (i <= k)%N].

Lemma prefix_set_card n (k : 'I_n.+1) : #|prefix_set k| = (val k).+1.
Proof.
have he : (\sum_(i : 'I_n.+1 | (i <= k)%N) 1 =
    \sum_(i : 'I_(val k).+1) 1)%N.
  exact (big_ord_narrow_leq (n1:=val k) (n2:=n) (F:=fun _ => 1%N) (ltn_ord k)).
rewrite /prefix_set cardsE -sum1_card he.
by rewrite sum1_card card_ord.
Qed.

Lemma prefix_set_nonempty n (k : 'I_n.+1) : (0 < #|prefix_set k|)%N.
Proof. by rewrite prefix_set_card. Qed.

Lemma prefix_set_subset n (a b : 'I_n.+1) (hab : (a <= b)%N) :
  prefix_set a \subset prefix_set b.
Proof.
apply/fintype.subsetP => i; rewrite !inE => hi.
exact: leq_trans hi hab.
Qed.

Section Cells.
Variable Real : realType.

Lemma affine_prefix_average n m (v : 'I_n.+1 -> simplex Real m)
    (p : {perm 'I_n.+1}) (k : 'I_n.+1) j :
  coordinate (affine_simplex v (prefix_barycenter Real p k)) j =
    mesh_average (prefix_set k) (fun i => coordinate (v (p i)) j).
Proof.
rewrite affine_prefix_barycenter_coordinate /mesh_average prefix_set_card.
congr (_ * _); apply: eq_bigl => i; by rewrite inE.
Qed.

Lemma affine_prefix_distance_ordered n m (v : 'I_n.+1 -> simplex Real m)
    (p : {perm 'I_n.+1}) D (hD : 0 <= D)
    (h : forall i j, simplex_distance (v i) (v j) <= D)
    (a b : 'I_n.+1) (hab : (a <= b)%N) :
  simplex_distance (affine_simplex v (prefix_barycenter Real p a))
    (affine_simplex v (prefix_barycenter Real p b)) <= mesh_factor Real n * D.
Proof.
have hq : 0 <= mesh_factor Real n * D := mulr_ge0 (mesh_factor_nonnegative Real n) hD.
apply: (simplex_distance_le hq) => j; rewrite !affine_prefix_average.
apply: (@mesh_average_nested_dimension_bound Real [the finType of 'I_n.+1]
  (prefix_set a) (prefix_set b) n (prefix_set_nonempty a)
  (prefix_set_subset hab) _ (fun i => coordinate (v (p i)) j) D hD).
- by rewrite prefix_set_card; exact: ltn_ord.
- move=> i _ k _.
  exact (le_trans (simplex_coordinate_distance_le (v (p i)) (v (p k)) j) (h (p i) (p k))).
Qed.

Lemma affine_prefix_distance_bound n m (v : 'I_n.+1 -> simplex Real m)
    (p : {perm 'I_n.+1}) D (hD : 0 <= D)
    (h : forall i j, simplex_distance (v i) (v j) <= D) (a b : 'I_n.+1) :
  simplex_distance (affine_simplex v (prefix_barycenter Real p a))
    (affine_simplex v (prefix_barycenter Real p b)) <= mesh_factor Real n * D.
Proof.
case: (leqP a b) => hab.
- exact (@affine_prefix_distance_ordered n m v p D hD h a b hab).
- rewrite simplex_distance_symmetric.
  exact (@affine_prefix_distance_ordered n m v p D hD h b a (ltnW hab)).
Qed.

Definition subdivided_vertices n m (v : 'I_n.+1 -> simplex Real m)
    (p : {perm 'I_n.+1}) (k : 'I_n.+1) :=
  affine_simplex v (prefix_barycenter Real p k).

Lemma subdivided_vertices_mesh_bound n m (v : 'I_n.+1 -> simplex Real m)
    (p : {perm 'I_n.+1}) :
  vertex_mesh (subdivided_vertices v p) <= mesh_factor Real n * vertex_mesh v.
Proof.
apply: vertex_mesh_le.
- exact (mulr_ge0 (mesh_factor_nonnegative Real n) (vertex_mesh_nonnegative v)).
- move=> a b; exact (@affine_prefix_distance_bound n m v p (vertex_mesh v)
    (vertex_mesh_nonnegative v) (vertex_distance_le_mesh v) a b).
Qed.

Lemma affine_barycentric_cell_composition n m (v : 'I_n.+1 -> simplex Real m)
    (p : {perm 'I_n.+1}) (x : simplex Real n) :
  affine_simplex v (barycentric_cell Real p x) = affine_simplex (subdivided_vertices v p) x.
Proof. exact: affine_simplex_composition. Qed.

Lemma affine_barycentric_cell_distance_bound n m (v : 'I_n.+1 -> simplex Real m)
    (p : {perm 'I_n.+1}) (x y : simplex Real n) :
  simplex_distance (affine_simplex v (barycentric_cell Real p x))
    (affine_simplex v (barycentric_cell Real p y)) <= mesh_factor Real n * vertex_mesh v.
Proof.
rewrite !affine_barycentric_cell_composition.
exact (le_trans (affine_simplex_distance_le_mesh _ _ _) (subdivided_vertices_mesh_bound v p)).
Qed.

Lemma affine_barycentric_cell_zero_distance m (v : 'I_1 -> simplex Real m)
    (p : {perm 'I_1}) (x y : simplex Real 0) :
  simplex_distance (affine_simplex v (barycentric_cell Real p x))
    (affine_simplex v (barycentric_cell Real p y)) = 0.
Proof.
apply/eqP; rewrite eq_le simplex_distance_nonnegative andbT.
have h := affine_barycentric_cell_distance_bound v p x y.
by rewrite mesh_factor_zero mul0r in h.
Qed.

End Cells.
End DPSingularSubdivisionMeshCells.
