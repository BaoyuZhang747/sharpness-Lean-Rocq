(** Actual natural chain homotopy from barycentric subdivision to the identity. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex TopologicalCategory TopologicalSimplexBasic
  SingularSet SingularCohomology SingularModelOperators SingularSubdivisionOperators
  SingularSubdivisionBoundary SingularSubdivisionHomotopyModels.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPTopological DPTopologicalSimplex
  DPSingularSet DPSingularCohomology DPSingularModelOperators DPSingularSubdivision
  DPSingularSubdivisionBoundary DPSingularSubdivisionHomotopyModels.
Local Open Scope ring_scope.

Module DPSingularSubdivisionHomotopy.
Section Homotopy.
Variable Real : realType.
Variable R : pzRingType.

Definition subdivision_homotopy_at n (X : topologicalType) :=
  model_operator (universal_homotopy_chain Real R n) X.

Definition subdivision_homotopy (X : topologicalType) :
    chain_homotopy (subdivision_chain_map Real R X) (chain_identity (singular_chains Real R X)).
Proof.
refine (@ChainHomotopy R _ _ _ _ (fun n => subdivision_homotopy_at n X) _ _).
- move=> x; change (chain_d (singular_chains Real R X) 0
    (model_operator (universal_homotopy_chain Real R 0) X x) = subdivision_at Real R X 0 x - x).
  by rewrite universal_homotopy_chain_zero model_operator_zero linear0 subdivision_degree_zero subrr.
- move=> n x; exact (@universal_homotopy_chain_succ Real R n X x).
Defined.

Theorem subdivision_homotopy_naturality n (X Y : topologicalType)
    (f : hom topological_category X Y) (x : chain_term (singular_chains Real R X) n) :
  chain_map_at (singular_chain_map Real R f) n.+1 (subdivision_homotopy_at n X x) =
    subdivision_homotopy_at n Y (chain_map_at (singular_chain_map Real R f) n x).
Proof. exact: model_operator_naturality. Qed.

End Homotopy.
End DPSingularSubdivisionHomotopy.

