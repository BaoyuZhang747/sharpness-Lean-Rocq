(** Universe-polymorphic wrapper for actual columnwise comparison for total and diagonal bisimplicial chains. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category.
From DiazParkV16b Require Import CategoryInducedBarCofinality.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws ChainQuasiIsoCriterion
  SimplicialChains SimplicialChainsMaps BisimplicialSet BisimplicialChains BisimplicialAlexanderWhitneyChain
  BisimplicialAlexanderWhitneyNaturality BisimplicialAlexanderWhitneyEquivalencePoly
  FirstQuadrantChainTotalMaps FirstQuadrantChainComparison.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPChainQuasiIsoCriterion
  DPSimplicialChains DPSimplicialChainMaps DPBisimplicialSet DPBisimplicialChains DPAlexanderWhitneyChain
  DPAlexanderWhitneyNaturality DPAlexanderWhitneyEquivalencePoly
  DPFirstQuadrantChainTotalMaps DPFirstQuadrantChainComparison.

Module DPBisimplicialChainComparisonPoly.
Section Comparison.
Variable R : pzRingType.
Variables X Y : bisimplicial_set.
Variable a : bisimplicial_map X Y.
Theorem bisimplicial_total_quasi_isomorphism
  (h : forall p, quasi_isomorphism (chain_map_of R (component a p))) :
  quasi_isomorphism (total_chains_map R a).
Proof.
apply: total_map_quasi_isomorphism => p.
apply: quasi_isomorphism_of_cycle_lift.
- move=> n x hx hb.
  exact (@quasi_iso_boundary_reflect R (chains R (fobj X p)) (chains R (fobj Y p))
    (chain_map_of R (component a p)) (h p) n x hx hb).
- move=> n y hy.
  exact (@quasi_iso_cycle_lift R (chains R (fobj X p)) (chains R (fobj Y p))
    (chain_map_of R (component a p)) (h p) n y hy).
Qed.
Theorem bisimplicial_diagonal_quasi_isomorphism_of_total
  (h : quasi_isomorphism (total_chains_map R a)) :
  quasi_isomorphism (diagonal_chains_map R a).
Proof.
apply (@quasi_isomorphism_cancel_second R _ _ _ (diagonal_chains_map R a) (alexander_whitney R Y)).
- exact (@alexander_whitney_quasi_isomorphism R Y).
- apply (@quasi_isomorphism_ext R _ _
    (chain_composition (alexander_whitney R X) (total_chains_map R a))
    (chain_composition (diagonal_chains_map R a) (alexander_whitney R Y))).
  + move=> n x; exact: alexander_whitney_natural.
  + apply: quasi_isomorphism_composition; [exact: alexander_whitney_quasi_isomorphism|exact h].
Qed.
Theorem bisimplicial_diagonal_quasi_isomorphism
  (h : forall p, quasi_isomorphism (chain_map_of R (component a p))) :
  quasi_isomorphism (diagonal_chains_map R a).
Proof. apply: bisimplicial_diagonal_quasi_isomorphism_of_total; exact: bisimplicial_total_quasi_isomorphism. Qed.
End Comparison.
End DPBisimplicialChainComparisonPoly.
