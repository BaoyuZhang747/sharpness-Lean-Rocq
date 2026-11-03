(** Literal iterated barycentric cells and their quantitative mesh bounds. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalSimplexBasic TopologicalSimplexCompact
  SingularSubdivisionGeometryAffine SingularSubdivisionGeometryBarycenter
  SingularSubdivisionMeshAffine SingularSubdivisionMeshFactor SingularSubdivisionMeshCells.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopologicalSimplex DPTopologicalSimplexCompact DPSingularSubdivisionAffine
  DPSingularSubdivisionBarycenter DPSingularSubdivisionMeshAffine
  DPSingularSubdivisionMeshFactor DPSingularSubdivisionMeshCells.
Local Open Scope ring_scope.

Module DPSingularSubdivisionMeshIterates.
Section Iterates.
Variable Real : realType.

Lemma simplex_distance_le_one n (x y : simplex Real n) : simplex_distance x y <= 1.
Proof.
apply (@simplex_distance_le Real n x y 1 ler01); move=> j.
rewrite ler_distl; apply/andP; split.
- have h0 : coordinate y j - 1 <= 0 by rewrite subr_le0; exact: coordinate_le1.
  exact (le_trans h0 (coordinate_ge0 x j)).
- apply: (le_trans (coordinate_le1 x j)).
  by rewrite lerDr; exact: coordinate_ge0.
Qed.

Lemma vertex_mesh_le_one n m (v : 'I_n.+1 -> simplex Real m) : vertex_mesh v <= 1.
Proof. apply: vertex_mesh_le => // i j; exact: simplex_distance_le_one. Qed.

Fixpoint iterated_vertices {n m} (v : 'I_n.+1 -> simplex Real m)
    (ps : seq {perm 'I_n.+1}) : 'I_n.+1 -> simplex Real m :=
  match ps with
  | [::] => v
  | p :: rest => subdivided_vertices (iterated_vertices v rest) p
  end.

Definition iterated_affine_cell n m (v : 'I_n.+1 -> simplex Real m)
    (ps : seq {perm 'I_n.+1}) :
    continuousType (simplex_space Real n) (simplex_space Real m) :=
  affine_simplex_map (iterated_vertices v ps).

Lemma iterated_affine_cell_nil n m (v : 'I_n.+1 -> simplex Real m) x :
  iterated_affine_cell v [::] x = affine_simplex v x.
Proof. reflexivity. Qed.

Lemma iterated_affine_cell_cons n m (v : 'I_n.+1 -> simplex Real m)
    p ps (x : simplex Real n) :
  iterated_affine_cell v (p :: ps) x =
    iterated_affine_cell v ps (barycentric_cell Real p x).
Proof. symmetry; exact: affine_barycentric_cell_composition. Qed.

Lemma iterated_vertices_mesh_bound n m (v : 'I_n.+1 -> simplex Real m) ps :
  vertex_mesh (iterated_vertices v ps) <= mesh_factor Real n ^+ size ps * vertex_mesh v.
Proof.
elim: ps => [|p ps ih]; first by rewrite /= expr0 mul1r.
change (vertex_mesh (subdivided_vertices (iterated_vertices v ps) p) <=
  mesh_factor Real n ^+ (size ps).+1 * vertex_mesh v).
apply: (le_trans (subdivided_vertices_mesh_bound _ _)).
rewrite exprS -mulrA.
exact (ler_wpM2l (mesh_factor_nonnegative Real n) ih).
Qed.

Lemma iterated_affine_cell_distance_bound n m (v : 'I_n.+1 -> simplex Real m)
    ps (x y : simplex Real n) :
  simplex_distance (iterated_affine_cell v ps x) (iterated_affine_cell v ps y) <=
    mesh_factor Real n ^+ size ps * vertex_mesh v.
Proof.
exact (le_trans (affine_simplex_distance_le_mesh (iterated_vertices v ps) x y)
  (iterated_vertices_mesh_bound v ps)).
Qed.

Lemma iterated_affine_cell_uniform_bound n m (v : 'I_n.+1 -> simplex Real m)
    ps (x y : simplex Real n) :
  simplex_distance (iterated_affine_cell v ps x) (iterated_affine_cell v ps y) <=
    mesh_factor Real n ^+ size ps.
Proof.
apply: (le_trans (iterated_affine_cell_distance_bound v ps x y)).
rewrite -{2}[mesh_factor Real n ^+ size ps]mulr1.
apply: (ler_wpM2l _ (vertex_mesh_le_one v)).
exact: exprn_ge0 (mesh_factor_nonnegative Real n).
Qed.

Definition iterated_barycentric_cell n (ps : seq {perm 'I_n.+1}) :=
  iterated_affine_cell (fun j => vertex Real j) ps.

Lemma iterated_barycentric_cell_nil n (x : simplex Real n) :
  iterated_barycentric_cell [::] x = x.
Proof. exact: affine_simplex_identity. Qed.

Lemma iterated_barycentric_cell_cons n (p : {perm 'I_n.+1}) ps (x : simplex Real n) :
  iterated_barycentric_cell (p :: ps) x =
    iterated_barycentric_cell ps (barycentric_cell Real p x).
Proof. exact: iterated_affine_cell_cons. Qed.

Lemma iterated_barycentric_cell_distance_bound n (ps : seq {perm 'I_n.+1})
    (x y : simplex Real n) :
  simplex_distance (iterated_barycentric_cell ps x) (iterated_barycentric_cell ps y) <=
    mesh_factor Real n ^+ size ps.
Proof. exact: iterated_affine_cell_uniform_bound. Qed.

Lemma iterated_affine_cell_zero_distance m (v : 'I_1 -> simplex Real m)
    ps (x y : simplex Real 0) :
  simplex_distance (iterated_affine_cell v ps x) (iterated_affine_cell v ps y) = 0.
Proof.
apply/eqP; rewrite eq_le simplex_distance_nonnegative andbT.
have h := iterated_affine_cell_distance_bound v ps x y.
by rewrite vertex_mesh_zero_dimension mulr0 in h.
Qed.

End Iterates.
End DPSingularSubdivisionMeshIterates.
