(** Literal finite-support direct sums are the chains of arbitrary simplicial copowers. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule CategoryModuleDirectSums.
From DiazParkV16b Require Import ChainComplex ChainDirectSum ChainQuasiIsomorphism
  ChainQuasiIsomorphismLaws SimplicialSet SimplicialCopower SimplicialChains SimplicialChainsMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainDirectSum
  DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPSimplicialSet DPSimplicialCopower DPSimplicialChains DPSimplicialChainMaps.
Local Open Scope ring_scope.
Module DPSimplicialCopowerChains.
Section Copower.
Variable R : pzRingType.
Variable I : Type.
Variable X : simplicial_set.
Let S := direct_sum (fun _ : I => chains R X).
Let C := chains R (copower I X).

Definition copower_chains_at n : {linear chain_term S n -> chain_term C n} :=
  (sum_lift (fun i => map_at R (@copower_inclusion I X i) n) : {linear _ -> _}).
Lemma copower_chains_at_single n i (x : chain_term (chains R X) n) :
  copower_chains_at n (@sum_single R I (fun _ => chain_term (chains R X) n) i x) =
    map_at R (@copower_inclusion I X i) n x.
Proof. exact: sum_lift_single. Qed.

Lemma copower_chains_at_commutes n x :
  chain_d C n (copower_chains_at n.+1 x) = copower_chains_at n (chain_d S n x).
Proof.
rewrite -[x](sum_generation x).
rewrite (linear_sum (copower_chains_at n.+1)) (linear_sum (chain_d C n))
  (linear_sum (chain_d S n)) (linear_sum (copower_chains_at n)).
apply: eq_bigr => i _.
rewrite copower_chains_at_single direct_sum_d_single copower_chains_at_single.
exact: map_boundary.
Qed.
Definition copower_chains : chain_map S C :=
  @ChainMap R S C copower_chains_at copower_chains_at_commutes.

Definition copower_chains_inverse_at n : {linear chain_term C n -> chain_term S n} :=
  (free_lift (fun p : simplex (copower I X) n =>
    @sum_single R I (fun _ => chain_term (chains R X) n) p.1 (free_basis R p.2)) : {linear _ -> _}).

Lemma copower_chains_inverse_single n i (x : chain_term (chains R X) n) :
  copower_chains_inverse_at n (map_at R (@copower_inclusion I X i) n x) =
    @sum_single R I (fun _ => chain_term (chains R X) n) i x.
Proof.
apply: (free_lift_ext
  (g := (copower_chains_inverse_at n \o map_at R (@copower_inclusion I X i) n : {linear _ -> _}))
  (h := (@sum_single R I (fun _ => chain_term (chains R X) n) i : {linear _ -> _}))).
move=> s.
change (copower_chains_inverse_at n (map_at R (@copower_inclusion I X i) n (free_basis R s)) =
  @sum_single R I (fun _ => chain_term (chains R X) n) i (free_basis R s)).
rewrite map_at_basis /copower_chains_inverse_at.
exact (@free_lift_basis R (simplex (copower I X) n) (chain_term S n)
  (fun p => @sum_single R I (fun _ => chain_term (chains R X) n) p.1 (free_basis R p.2)) (i,s)).
Qed.

Lemma copower_chains_forwardK n (x : chain_term S n) :
  copower_chains_inverse_at n (chain_map_at copower_chains n x) = x.
Proof.
change (copower_chains_inverse_at n (copower_chains_at n x) = x).
rewrite -[x](sum_generation x) (linear_sum (copower_chains_at n))
  (linear_sum (copower_chains_inverse_at n)).
apply: eq_bigr => i _.
rewrite copower_chains_at_single; exact: copower_chains_inverse_single.
Qed.

Lemma copower_chains_inverseK n (x : chain_term C n) :
  chain_map_at copower_chains n (copower_chains_inverse_at n x) = x.
Proof.
apply: (free_lift_ext
  (g := (chain_map_at copower_chains n \o copower_chains_inverse_at n : {linear _ -> _}))
  (h := (idfun : {linear chain_term C n -> chain_term C n}))).
move=> [i s].
change (copower_chains_at n (copower_chains_inverse_at n (free_basis R (i,s))) = free_basis R (i,s)).
have ee := @free_lift_basis R (simplex (copower I X) n) (chain_term S n)
  (fun p => @sum_single R I (fun _ => chain_term (chains R X) n) p.1 (free_basis R p.2)) (i,s).
change (copower_chains_at n (free_lift
  (fun p : simplex (copower I X) n => @sum_single R I (fun _ => chain_term (chains R X) n) p.1 (free_basis R p.2))
  (free_basis R (i,s))) = free_basis R (i,s)).
rewrite ee.
change (copower_chains_at n
  (@sum_single R I (fun _ => chain_term (chains R X) n) i (free_basis R s)) = free_basis R (i,s)).
by rewrite copower_chains_at_single map_at_basis.
Qed.

Lemma copower_chains_injective n : injective (chain_map_at copower_chains n).
Proof. exact: (can_inj (copower_chains_forwardK (n := n))). Qed.
Lemma copower_chains_surjective n y : exists x, chain_map_at copower_chains n x = y.
Proof. exists (copower_chains_inverse_at n y); exact: copower_chains_inverseK. Qed.
Theorem copower_chains_quasi_isomorphism : quasi_isomorphism copower_chains.
Proof.
apply: degreewise_bijective_quasi_isomorphism;
  [exact: copower_chains_injective | exact: copower_chains_surjective].
Qed.
End Copower.
End DPSimplicialCopowerChains.
