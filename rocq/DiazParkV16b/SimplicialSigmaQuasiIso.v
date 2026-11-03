(** Pointwise native chain quasi-isomorphisms give a native quasi-isomorphism of arbitrary simplicial disjoint unions. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModuleDirectSums.
From DiazParkV16b Require Import ChainComplex ChainDirectSum ChainDirectSumQuasiIso
  ChainQuasiIsomorphism ChainQuasiIsomorphismLaws SimplicialSet SimplicialSigma
  SimplicialChains SimplicialChainsMaps SimplicialSigmaChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainDirectSum DPChainDirectSumQuasiIso
  DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialSet
  DPSimplicialSigma DPSimplicialChains DPSimplicialChainMaps DPSimplicialSigmaChains.
Local Open Scope ring_scope.

Module DPSimplicialSigmaQuasiIso.
Section Sigma.
Variable R : pzRingType.
Variable I : Type.
Variables X Y : I -> simplicial_set.
Variable f : forall i, simplicial_map (X i) (Y i).
Lemma sigma_chains_natural n (x : chain_term (direct_sum (fun i => chains R (X i))) n) :
  map_at R (sigma_map f) n (chain_map_at (sigma_chains R X) n x) =
    chain_map_at (sigma_chains R Y) n (chain_map_at (direct_sum_map (fun i => chain_map_of R (f i))) n x).
Proof.
change (map_at R (sigma_map f) n (sigma_chains_at R X n x) =
  sigma_chains_at R Y n (chain_map_at (direct_sum_map (fun i => chain_map_of R (f i))) n x)).
rewrite -[x](sum_generation x).
rewrite (linear_sum (sigma_chains_at R X n)) (linear_sum (map_at R (sigma_map f) n))
  (linear_sum (chain_map_at (direct_sum_map (fun i => chain_map_of R (f i))) n))
  (linear_sum (sigma_chains_at R Y n)).
apply: eq_bigr => i _.
rewrite sigma_chains_at_single direct_sum_map_single sigma_chains_at_single.
change (map_at R (sigma_map f) n (map_at R (sigma_inclusion X i) n (sum_coefficient x i)) =
  map_at R (sigma_inclusion Y i) n (map_at R (f i) n (sum_coefficient x i))).
by rewrite -!map_composition sigma_map_inclusion.
Qed.
Theorem sigma_map_quasi_isomorphism (hf : forall i, quasi_isomorphism (chain_map_of R (f i))) :
  quasi_isomorphism (chain_map_of R (sigma_map f)).
Proof.
apply (@quasi_isomorphism_cancel_first R _ _ _ (sigma_chains R X) (chain_map_of R (sigma_map f))).
- exact: sigma_chains_quasi_isomorphism.
- apply (@quasi_isomorphism_ext R _ _
    (chain_composition (direct_sum_map (fun i => chain_map_of R (f i))) (sigma_chains R Y))
    (chain_composition (sigma_chains R X) (chain_map_of R (sigma_map f)))).
  + move=> n x; symmetry; exact: sigma_chains_natural.
  + apply: quasi_isomorphism_composition.
    * exact: direct_sum_quasi_isomorphism hf.
    * exact: sigma_chains_quasi_isomorphism.
Qed.
End Sigma.
End DPSimplicialSigmaQuasiIso.
