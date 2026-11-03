(** Arbitrary simplicial copowers preserve the actual chain quasi-isomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule CategoryModuleDirectSums.
From DiazParkV16b Require Import ChainComplex ChainDirectSum ChainDirectSumQuasiIso
  ChainQuasiIsomorphism ChainQuasiIsomorphismLaws SimplicialSet SimplicialCopower
  SimplicialChains SimplicialChainsMaps SimplicialCopowerChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainDirectSum DPChainDirectSumQuasiIso
  DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialSet DPSimplicialCopower
  DPSimplicialChains DPSimplicialChainMaps DPSimplicialCopowerChains.
Local Open Scope ring_scope.
Module DPSimplicialCopowerQuasiIso.
Section Maps.
Variable R : pzRingType.
Variable I : Type.
Variables X Y : simplicial_set.
Variable a : simplicial_map X Y.
Let F := chain_map_of R a.
Let SF := direct_sum_map (fun _ : I => F).
Let CF := chain_map_of R (@copower_map I X Y a).

Lemma copower_chains_natural_single n i (x : chain_term (chains R X) n) :
  chain_map_at CF n (map_at R (@copower_inclusion I X i) n x) =
    map_at R (@copower_inclusion I Y i) n (chain_map_at F n x).
Proof.
apply: (free_lift_ext
  (g := (chain_map_at CF n \o map_at R (@copower_inclusion I X i) n : {linear _ -> _}))
  (h := (map_at R (@copower_inclusion I Y i) n \o chain_map_at F n : {linear _ -> _}))).
move=> s.
change (map_at R (@copower_map I X Y a) n (map_at R (@copower_inclusion I X i) n (free_basis R s)) =
  map_at R (@copower_inclusion I Y i) n (map_at R a n (free_basis R s))).
by rewrite !map_at_basis.
Qed.

Lemma copower_chains_natural n (x : chain_term (direct_sum (fun _ : I => chains R X)) n) :
  chain_map_at CF n (chain_map_at (copower_chains R I X) n x) =
    chain_map_at (copower_chains R I Y) n (chain_map_at SF n x).
Proof.
change (chain_map_at CF n (copower_chains_at R I X n x) =
  copower_chains_at R I Y n (chain_map_at SF n x)).
rewrite -[x](sum_generation x)
  (linear_sum (copower_chains_at R I X n)) (linear_sum (chain_map_at CF n))
  (linear_sum (chain_map_at SF n)) (linear_sum (copower_chains_at R I Y n)).
apply: eq_bigr => i _.
rewrite copower_chains_at_single direct_sum_map_single copower_chains_at_single.
exact: copower_chains_natural_single.
Qed.

Theorem copower_map_quasi_isomorphism (ha : quasi_isomorphism F) : quasi_isomorphism CF.
Proof.
apply: (@quasi_isomorphism_cancel_first R _ _ _ (copower_chains R I X) CF).
- exact: copower_chains_quasi_isomorphism.
- apply: (@quasi_isomorphism_ext R _ _
    (chain_composition SF (copower_chains R I Y))
    (chain_composition (copower_chains R I X) CF)).
  + move=> n x; symmetry; exact: copower_chains_natural.
  + apply: quasi_isomorphism_composition.
    * apply: direct_sum_quasi_isomorphism; by move=> i.
    * exact: copower_chains_quasi_isomorphism.
Qed.
End Maps.
End DPSimplicialCopowerQuasiIso.
