(** Actual uniform quantitative decay of all iterated barycentric cells. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology normedtype sequences.
From DiazParkV16b Require Import TopologicalSimplexBasic
  SingularSubdivisionMeshAffine SingularSubdivisionMeshFactor SingularSubdivisionMeshIterates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopologicalSimplex DPSingularSubdivisionMeshAffine
  DPSingularSubdivisionMeshFactor DPSingularSubdivisionMeshIterates.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularSubdivisionMeshDecay.
Section Decay.
Variable Real : realType.

Lemma mesh_factor_powers_tendsto_zero n :
  (fun r : nat => mesh_factor Real n ^+ r) @ \oo --> (0 : Real).
Proof.
apply: cvg_expr.
by rewrite ger0_norm ?mesh_factor_nonnegative //; exact: mesh_factor_lt_one.
Qed.

Lemma mesh_factor_powers_eventually_lt n (eps : Real) (heps : 0 < eps) :
  exists N : nat, forall r : nat, (N <= r)%N -> mesh_factor Real n ^+ r < eps.
Proof.
have hnear : \forall r \near \oo, `|mesh_factor Real n ^+ r| < eps.
  exact (cvgr0_norm_lt (fun r : nat => mesh_factor Real n ^+ r)
    (mesh_factor_powers_tendsto_zero n) eps heps).
case: hnear => N _ hN; exists N => r hr.
have h := hN r hr.
by rewrite ger0_norm ?exprn_ge0 ?mesh_factor_nonnegative in h.
Qed.

Lemma iterated_affine_cells_uniformly_small n m (v : 'I_n.+1 -> simplex Real m)
    (eps : Real) (heps : 0 < eps) :
  exists N : nat, forall (ps : seq {perm 'I_n.+1}), (N <= size ps)%N ->
    forall x y : simplex Real n,
      simplex_distance (iterated_affine_cell v ps x) (iterated_affine_cell v ps y) < eps.
Proof.
case: (mesh_factor_powers_eventually_lt n heps) => N hN.
exists N => ps hps x y.
exact (le_lt_trans (iterated_affine_cell_uniform_bound v ps x y) (hN (size ps) hps)).
Qed.

Lemma iterated_barycentric_cells_uniformly_small n (eps : Real) (heps : 0 < eps) :
  exists N : nat, forall (ps : seq {perm 'I_n.+1}), (N <= size ps)%N ->
    forall x y : simplex Real n,
      simplex_distance (iterated_barycentric_cell Real ps x)
        (iterated_barycentric_cell Real ps y) < eps.
Proof. exact: iterated_affine_cells_uniformly_small. Qed.

End Decay.
End DPSingularSubdivisionMeshDecay.
