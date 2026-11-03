(** Objectwise actual chain equivalences induce equivalences of the literal simplicial replacement total and diagonal. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve
  ChainComplex ChainQuasiIsomorphism ChainQuasiIsoCriterion SimplicialChains SimplicialChainsMaps
  SimplicialSigma SimplicialSigmaQuasiIso BisimplicialSet BisimplicialChains
  BisimplicialAlexanderWhitneyNaturality BisimplicialChainComparisonPoly
  SimplicialReplacementTypes SimplicialReplacement SimplicialReplacementMaps.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve
  DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsoCriterion DPSimplicialChains DPSimplicialChainMaps
  DPSimplicialSigma DPSimplicialSigmaQuasiIso DPBisimplicialSet DPBisimplicialChains
  DPAlexanderWhitneyNaturality DPBisimplicialChainComparisonPoly
  DPSimplicialReplacementTypes DPSimplicialReplacement DPSimplicialReplacementMaps.

Module DPSimplicialReplacementComparisonPoly.
Section Comparison.
Variable R : pzRingType.
Variable C : category.
Variables F G : functor C simplicial_category.
Variable a : nat_trans F G.
Hypothesis ha : forall c, quasi_isomorphism (chain_map_of R (component a c)).
Definition column_family (H : functor C simplicial_category) p :=
  fun s : simplex (nerve C) p => fobj H (initial_object s).
Arguments column_family H p _ : clear implicits.

Lemma replacement_column_sigma_terms p q :
  simplex (replacement_column F p) q = simplex (sigma_set (column_family F p)) q.
Proof. reflexivity. Qed.
Lemma replacement_column_sigma_d p q x :
  @DPSimplicialChains.boundary R (replacement_column F p) q x =
    @DPSimplicialChains.boundary R (sigma_set (column_family F p)) q x.
Proof. reflexivity. Qed.
Lemma replacement_column_sigma_map p q x :
  map_at R (replacement_map_column a p) q x =
    map_at R (sigma_map (fun s : simplex (nerve C) p => component a (initial_object s))) q x.
Proof. reflexivity. Qed.

Theorem replacement_column_quasi_isomorphism p :
  quasi_isomorphism (chain_map_of R (replacement_map_column a p)).
Proof.
have hs := @sigma_map_quasi_isomorphism R (simplex (nerve C) p)
  (column_family F p) (column_family G p)
  (fun s => component a (initial_object s)) (fun s => ha (initial_object s)).
apply: quasi_isomorphism_of_cycle_lift.
- move=> n x hx hb.
  exact (@quasi_iso_boundary_reflect R _ _
    (chain_map_of R (sigma_map (fun s : simplex (nerve C) p => component a (initial_object s)))) hs n x hx hb).
- move=> n y hy.
  exact (@quasi_iso_cycle_lift R _ _
    (chain_map_of R (sigma_map (fun s : simplex (nerve C) p => component a (initial_object s)))) hs n y hy).
Qed.
Theorem replacement_total_quasi_isomorphism :
  quasi_isomorphism (total_chains_map R (replacement_map a)).
Proof. apply: bisimplicial_total_quasi_isomorphism; exact: replacement_column_quasi_isomorphism. Qed.
Theorem replacement_diagonal_quasi_isomorphism :
  quasi_isomorphism (diagonal_chains_map R (replacement_map a)).
Proof. apply: bisimplicial_diagonal_quasi_isomorphism; exact: replacement_column_quasi_isomorphism. Qed.
End Comparison.
End DPSimplicialReplacementComparisonPoly.
