(** Positive exactness of actual representable total chains, using column comparison and the literal row-zero projection. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism SimplicialSet SimplicialChains
  StandardSimplexConeChains BisimplicialSet BisimplicialChains BisimplicialRepresentable
  BisimplicialRepresentableColumnComparison FirstQuadrantChainTotalMaps FirstQuadrantChainRowZeroTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainQuasiIsomorphism DPSimplicialSet DPSimplicialChains
  DPStandardSimplexConeChains DPBisimplicialSet DPBisimplicialChains DPBisimplicialRepresentable
  DPBisimplicialRepresentableColumnComparison DPFirstQuadrantChainTotalMaps DPFirstQuadrantChainRowZeroTotal.

Module DPBisimplicialRepresentableTotalExact.
Section Model.
Variable R : pzRingType.
Variables m n : nat.
Definition representable_total_simplex_map :
  chain_map (total_chains R (representable m n)) (chains R (standard_simplex m)) :=
  chain_composition (total_map (column_comparison R m n)) (total_projection (chains R (standard_simplex m))).

Theorem representable_total_positive_exact q (a : chain_term (total_chains R (representable m n)) q.+1) :
  @cycle R (total_chains R (representable m n)) q.+1 a ->
  @DPChainComplex.boundary R (total_chains R (representable m n)) q.+1 a.
Proof.
move=> ha.
apply: (quasi_iso_boundary_reflect (column_total_comparison_quasi_isomorphism R m n) ha).
have hc := chain_map_cycle (total_map (column_comparison R m n)) ha.
apply: (quasi_iso_boundary_reflect (total_projection_quasi_isomorphism (chains R (standard_simplex m))) hc).
apply: standard_simplex_positive_exact.
exact: chain_map_cycle hc.
Qed.
End Model.
End DPBisimplicialRepresentableTotalExact.
