(** Uniform containment of the actual iterated barycentric cells in an open cover. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalSimplexBasic TopologicalSimplexCompact
  SingularSubdivisionMeshAffine SingularSubdivisionMeshIterates SingularSubdivisionMeshDecay
  SingularSubdivisionSmallnessCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopologicalSimplex DPTopologicalSimplexCompact DPSingularSubdivisionMeshAffine
  DPSingularSubdivisionMeshIterates DPSingularSubdivisionMeshDecay
  DPSingularSubdivisionSmallnessCompact.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularSubdivisionSmallnessSimplex.
Section SimplexCover.
Variable Real : realType.

Lemma simplex_ball_distance n (x y : simplex Real n) (eps : Real) :
  @ball Real [the pseudoMetricType Real of simplex Real n] x eps y =
    (simplex_distance x y < eps).
Proof.
change (ball (simplex_vector x) eps (simplex_vector y) =
  (simplex_distance x y < eps)).
by rewrite mx_norm_ball /ball_ /simplex_distance.
Qed.

Lemma simplex_open_cover_uniform_ball n (I : Type)
    (U : I -> set (simplex_space Real n))
    (hopen : forall i, open (U i))
    (hcover : forall x, exists i, U i x) :
  exists2 eps : Real, 0 < eps &
    forall x : simplex Real n, exists i,
      forall y : simplex Real n, simplex_distance x y < eps -> U i y.
Proof.
have hc : forall x : simplex Real n, setT x -> exists i, U i x by move=> x _; exact: hcover.
case: (@compact_open_cover_uniform_ball Real
  [the pseudoMetricType Real of simplex Real n] I U setT
  (@DPTopologicalSimplexCompact.simplex_compact Real n) hopen hc) => eps heps h.
exists eps => // x; case: (h x Logic.I) => i hi; exists i => y hy.
apply: hi; by rewrite simplex_ball_distance.
Qed.

Theorem iterated_barycentric_cells_open_cover n (I : Type)
    (U : I -> set (simplex_space Real n))
    (hopen : forall i, open (U i))
    (hcover : forall x, exists i, U i x) :
  exists N : nat, forall (ps : seq {perm 'I_n.+1}), (N <= size ps)%N ->
    exists i, forall x : simplex Real n, U i (iterated_barycentric_cell Real ps x).
Proof.
case: (simplex_open_cover_uniform_ball hopen hcover) => eps heps hball.
case: (@iterated_barycentric_cells_uniformly_small Real n eps heps) => N hN.
exists N => ps hps.
case: (hball (iterated_barycentric_cell Real ps (vertex Real ord0))) => i hi.
exists i => x; apply: hi.
exact: (hN ps hps (vertex Real ord0) x).
Qed.

End SimplexCover.
End DPSingularSubdivisionSmallnessSimplex.
