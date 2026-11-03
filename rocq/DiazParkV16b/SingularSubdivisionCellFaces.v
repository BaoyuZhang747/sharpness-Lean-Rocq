(** Literal internal and outer faces of the actual singular barycentric cells. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities
  SimplicialSet SimplicialSetOperators SingularSet TopologicalCategory
  TopologicalSimplexBasic TopologicalSimplexAffine SingularSubdivisionGeometryAffine
  SingularSubdivisionGeometryBarycenter SingularSubdivisionGeometryFaces
  SingularSubdivisionMeshPrefix SingularSubdivisionOperators SubdivisionPermutationAdjacent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPTopological DPTopologicalSimplex DPTopologicalSimplexAffine
  DPSimplexCategory DPSimplexOperators DPSimplexIdentities DPSimplicialOperators DPSingularSet
  DPSingularSubdivisionAffine DPSingularSubdivisionBarycenter DPSingularSubdivisionFaces
  DPSingularSubdivisionMeshPrefix DPSingularSubdivision DPSubdivisionPermutationAdjacent.
Local Open Scope ring_scope.

Module DPSingularSubdivisionCellFaces.

Lemma coface_value_avoids (c i : nat) : coface_value c i <> c.
Proof. unfold coface_value; destruct (PeanoNat.Nat.leb_spec0 c i); lia. Qed.

Lemma coface_avoids n (c : 'I_n.+2) (i : 'I_n.+1) : coface c i != c.
Proof.
apply/eqP => e.
have ev := congr1 val e.
change (coface_value c i = val c) in ev.
exact (@coface_value_avoids (val c) (val i) ev).
Qed.

Section Geometry.
Variable Real : realType.

Lemma prefix_barycenter_adjacent n (j : 'I_n.+1) (p : {perm 'I_n.+2})
    (c : 'I_n.+2) (hc : c != vertex_widen j) :
  prefix_barycenter Real (adjacent_pair j p) c = prefix_barycenter Real p c.
Proof.
apply simplex_ext => k; rewrite !prefix_barycenter_coordinate_filtered.
congr (_ * _); exact (@adjacent_prefix_sum n j [the zmodType of (Real : Type)] c hc p (fun i => if k == i then 1 else 0)).
Qed.

Lemma barycentric_cell_internal_face n (j : 'I_n.+1) (p : {perm 'I_n.+2})
    (x : DPTopologicalSimplex.simplex Real n) :
  barycentric_cell Real (adjacent_pair j p) (pushforward (coface (vertex_widen j)) x) =
    barycentric_cell Real p (pushforward (coface (vertex_widen j)) x).
Proof.
change (affine_simplex (prefix_barycenter Real (adjacent_pair j p))
  (pushforward (coface (vertex_widen j)) x) =
  affine_simplex (prefix_barycenter Real p) (pushforward (coface (vertex_widen j)) x)).
rewrite !affine_simplex_precompose.
apply affine_simplex_ext_vertices => i.
apply prefix_barycenter_adjacent; exact: coface_avoids.
Qed.

End Geometry.

Section Singular.
Variable Real : realType.
Variable X : topologicalType.

Lemma singular_barycentric_cell_internal_face n (j : 'I_n.+1) (p : {perm 'I_n.+2})
    (s : DPSimplicialSet.simplex (singular_set Real X) n.+1) :
  face (singular_set Real X) (vertex_widen j) (singular_barycentric_cell (adjacent_pair j p) s) =
    face (singular_set Real X) (vertex_widen j) (singular_barycentric_cell p s).
Proof.
apply topological_hom_ext => x.
change (s (barycentric_cell Real (adjacent_pair j p)
    (pushforward (coface (vertex_widen j)) x)) =
  s (barycentric_cell Real p (pushforward (coface (vertex_widen j)) x))).
by rewrite barycentric_cell_internal_face.
Qed.

Lemma singular_barycentric_cell_outer_face n (p : {perm 'I_n.+2}) (q : {perm 'I_n.+1})
    (c : 'I_n.+2) (hp : forall j : 'I_n.+1, p (vertex_widen j) = coface c (q j))
    (s : DPSimplicialSet.simplex (singular_set Real X) n.+1) :
  face (singular_set Real X) ord_max (singular_barycentric_cell p s) =
    singular_barycentric_cell q (face (singular_set Real X) c s).
Proof.
apply topological_hom_ext => x.
change (s (barycentric_cell Real p (pushforward (coface ord_max) x)) =
  s (pushforward (coface c) (barycentric_cell Real q x))).
by rewrite (@barycentric_cell_outer_face Real n p q c hp x).
Qed.

End Singular.
End DPSingularSubdivisionCellFaces.




