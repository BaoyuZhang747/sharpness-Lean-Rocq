(** Positive exactness of actual singular chains on a contracted space. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalSimplexBasic TopologicalSimplexContraction SingularCohomology
  SingularPointChains SingularChainHomotopy SingularChainMapsLaws ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPTopological DPTopologicalHomotopy DPTopologicalSimplex
  DPTopologicalSimplexContraction DPSingularCohomology DPSingularPointChains
  DPSingularChainHomotopy DPSingularChainMapsLaws DPChainComplex.
Local Open Scope ring_scope.

Module DPSingularContractibleChains.
Section Contractible.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variable x0 : X.
Let constant : continuousType X X := [the continuousType X X of (cst x0)].
Variable H : continuous_homotopy Real (continuous_identity X) constant.

Definition point_inclusion : hom topological_category point_space X :=
  [the continuousType point_space X of (cst x0)].

Definition retract_homotopy : continuous_homotopy Real (continuous_identity X)
  (compose (point_map X) point_inclusion).
Proof.
refine (@ContinuousHomotopy Real X X _ _ (homotopy_map H) _ _).
- exact: homotopy_start.
- exact: homotopy_end.
Defined.

Theorem contractible_positive_exact n (x : chain_term (singular_chains Real R X) n.+1) :
  @cycle R (singular_chains Real R X) n.+1 x ->
  @boundary R (singular_chains Real R X) n.+1 x.
Proof.
move=> hx.
pose f := singular_chain_map Real R (point_map X).
pose g := singular_chain_map Real R point_inclusion.
have hp := @chain_map_cycle R _ _ f n.+1 x hx.
have [b hb] := @point_positive_exact Real R n (chain_map_at f n.+1 x) hp.
have [u hu] := @chain_homotopy_boundary R _ _ _ _
  (singular_chain_homotopy R retract_homotopy) n.+1 x hx.
exists (chain_map_at g n.+2 b - u).
rewrite linearB chain_map_commutes hb hu.
change (chain_map_at (singular_chain_map Real R point_inclusion) n.+1
  (chain_map_at (singular_chain_map Real R (point_map X)) n.+1 x) -
  (chain_map_at (singular_chain_map Real R (compose (point_map X) point_inclusion)) n.+1 x -
   chain_map_at (singular_chain_map Real R (continuous_identity X)) n.+1 x) = x).
rewrite -singular_chain_composition singular_chain_identity.
by rewrite opprB addrCA subrr addr0.
Qed.
End Contractible.

Section Simplex.
Variable Real : realType.
Variable R : pzRingType.

Theorem simplex_positive_exact d n
    (x : chain_term (singular_chains Real R (simplex_space Real d)) n.+1) :
  @cycle R (singular_chains Real R (simplex_space Real d)) n.+1 x ->
  @boundary R (singular_chains Real R (simplex_space Real d)) n.+1 x.
Proof.
exact: (@contractible_positive_exact Real R (simplex_space Real d)
  (@vertex Real d ord0) (simplex_contraction (@vertex Real d ord0)) n x).
Qed.
End Simplex.
End DPSingularContractibleChains.
