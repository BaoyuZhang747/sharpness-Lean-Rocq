(** Native chains of an arbitrary dependent simplicial family are its actual direct sum of chains. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule CategoryModuleDirectSums.
From DiazParkV16b Require Import ChainComplex ChainDirectSum ChainQuasiIsomorphism
  ChainQuasiIsomorphismLaws SimplicialSet SimplicialSigma SimplicialChains SimplicialChainsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainDirectSum
  DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialSet
  DPSimplicialSigma DPSimplicialChains DPSimplicialChainMaps.
Local Open Scope ring_scope.

Module DPSimplicialSigmaChains.
Section Sigma.
Variable R : pzRingType.
Variable I : Type.
Variable X : I -> simplicial_set.
Let S := direct_sum (fun i => chains R (X i)).
Let C := chains R (sigma_set X).

Definition sigma_chains_at n : {linear chain_term S n -> chain_term C n} :=
  (sum_lift (fun i => map_at R (sigma_inclusion X i) n) : {linear _ -> _}).
Lemma sigma_chains_at_single n i (x : chain_term (chains R (X i)) n) :
  sigma_chains_at n (@sum_single R I (fun j => chain_term (chains R (X j)) n) i x) =
    map_at R (sigma_inclusion X i) n x.
Proof. exact: sum_lift_single. Qed.
Lemma sigma_chains_at_commutes n x :
  chain_d C n (sigma_chains_at n.+1 x) = sigma_chains_at n (chain_d S n x).
Proof.
rewrite -[x](sum_generation x).
rewrite (linear_sum (sigma_chains_at n.+1)) (linear_sum (chain_d C n))
  (linear_sum (chain_d S n)) (linear_sum (sigma_chains_at n)).
apply: eq_bigr => i _.
rewrite sigma_chains_at_single direct_sum_d_single sigma_chains_at_single.
exact: map_boundary.
Qed.
Definition sigma_chains : chain_map S C :=
  @ChainMap R S C sigma_chains_at sigma_chains_at_commutes.

Definition sigma_chains_inverse_basis n (p : simplex (sigma_set X) n) : chain_term S n :=
  match p with existT i a => @sum_single R I (fun j => chain_term (chains R (X j)) n) i (free_basis R a) end.
Definition sigma_chains_inverse_at n : {linear chain_term C n -> chain_term S n} :=
  (free_lift (@sigma_chains_inverse_basis n) : {linear _ -> _}).
Lemma sigma_chains_inverse_basis_apply n i (a : simplex (X i) n) :
  sigma_chains_inverse_at n (free_basis R (existT _ i a)) =
    @sum_single R I (fun j => chain_term (chains R (X j)) n) i (free_basis R a).
Proof. exact: free_lift_basis. Qed.
Lemma sigma_chains_inverse_single n i (x : chain_term (chains R (X i)) n) :
  sigma_chains_inverse_at n (map_at R (sigma_inclusion X i) n x) =
    @sum_single R I (fun j => chain_term (chains R (X j)) n) i x.
Proof.
apply: (free_lift_ext
  (g := (sigma_chains_inverse_at n \o map_at R (sigma_inclusion X i) n : {linear _ -> _}))
  (h := (@sum_single R I (fun j => chain_term (chains R (X j)) n) i : {linear _ -> _}))).
move=> a.
change (sigma_chains_inverse_at n (map_at R (sigma_inclusion X i) n (free_basis R a)) =
  @sum_single R I (fun j => chain_term (chains R (X j)) n) i (free_basis R a)).
rewrite map_at_basis; exact: sigma_chains_inverse_basis_apply.
Qed.
Lemma sigma_chains_forwardK n (x : chain_term S n) :
  sigma_chains_inverse_at n (chain_map_at sigma_chains n x) = x.
Proof.
change (sigma_chains_inverse_at n (sigma_chains_at n x) = x).
rewrite -[x](sum_generation x) (linear_sum (sigma_chains_at n))
  (linear_sum (sigma_chains_inverse_at n)).
apply: eq_bigr => i _.
rewrite sigma_chains_at_single; exact: sigma_chains_inverse_single.
Qed.
Lemma sigma_chains_inverseK n (x : chain_term C n) :
  chain_map_at sigma_chains n (sigma_chains_inverse_at n x) = x.
Proof.
apply: (free_lift_ext
  (g := (chain_map_at sigma_chains n \o sigma_chains_inverse_at n : {linear _ -> _}))
  (h := (idfun : {linear chain_term C n -> chain_term C n}))).
move=> [i a].
change (sigma_chains_at n (sigma_chains_inverse_at n (free_basis R (existT _ i a))) =
  free_basis R (existT _ i a)).
by rewrite sigma_chains_inverse_basis_apply sigma_chains_at_single map_at_basis.
Qed.
Lemma sigma_chains_injective n : injective (chain_map_at sigma_chains n).
Proof. exact: (can_inj (sigma_chains_forwardK (n := n))). Qed.
Lemma sigma_chains_surjective n y : exists x, chain_map_at sigma_chains n x = y.
Proof. exists (sigma_chains_inverse_at n y); exact: sigma_chains_inverseK. Qed.
Theorem sigma_chains_quasi_isomorphism : quasi_isomorphism sigma_chains.
Proof.
apply: degreewise_bijective_quasi_isomorphism;
  [exact: sigma_chains_injective | exact: sigma_chains_surjective].
Qed.
End Sigma.
End DPSimplicialSigmaChains.
