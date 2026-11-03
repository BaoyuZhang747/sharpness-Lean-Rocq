(** Unconditional small-chain comparison for an arbitrary actual open cover. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category CategoryModules MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  SmallChainComparison SingularCohomology SingularSmallChains SingularSmallSubdivision
  SingularSubdivisionBoundary SingularSubdivisionHomotopy SingularSubdivisionEventual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainHomology DPChainHomologyMaps DPSmallChainComparison
  DPSingularCohomology DPSingularSmallChains DPSingularSmallSubdivision
  DPSingularSubdivisionBoundary DPSingularSubdivisionHomotopy DPSingularSubdivisionEventual.

Module DPSmallSingularChainComparison.
Section Comparison.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variable I : Type.
Variable U : I -> X -> Prop.
Variable hopen : forall i, open (U i).
Variable hcover : forall x, exists i, U i x.

Definition small_singular_homology_iso n : @isomorphism (module_category R)
    [the lmodType R of homology (@small_chains Real X I U R) n]
    [the lmodType R of homology (singular_chains Real R X) n] :=
  @comparison_iso R (@small_chains Real X I U R) (singular_chains Real R X)
    (@small_chain_inclusion Real X I U R)
    (@small_chain_inclusion_injective Real X I U R)
    (@small_subdivision_chain_map Real R X I U) (subdivision_chain_map Real R X)
    (@small_subdivision_inclusion Real R X I U)
    (@small_subdivision_homotopy Real R X I U) (subdivision_homotopy Real R X)
    (@chain_eventually_small Real R X I U hopen hcover) n.

Theorem small_singular_homology_iso_hom n (q : homology (@small_chains Real X I U R) n) :
  module_hom_fun (iso_hom (small_singular_homology_iso n)) q =
  homology_map (@small_chain_inclusion Real X I U R) n q.
Proof. reflexivity. Qed.
End Comparison.
End DPSmallSingularChainComparison.
