(** Literal subspace-to-small maps and the actual intersection--union quotient data. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainShortExact SimplicialSet SimplicialSubcomplex
  SimplicialChains SimplicialChainsMaps SingularSet SingularCohomology SingularSmallChains
  SingularChainExcisionSubspaces SingularChainExcisionSubspacesLattice SingularChainExcisionSubspacesExact
  SingularExcisionSequence SingularExcisionSequenceLiteral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainShortExact DPSimplicialSet DPSimplicialSubcomplex
  DPSimplicialChains DPSimplicialChainMaps DPSingularSet DPSingularCohomology DPSingularSmallChains
  DPSingularChainExcisionSubspaces DPSingularChainExcisionSubspacesLattice DPSingularChainExcisionSubspacesExact
  DPSingularExcisionSequence DPSingularExcisionSequenceLiteral.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularExcisionSmallMaps.
Section SmallMaps.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variables A B : set X.
Let SA := singular_chains Real R (subset_space A).
Let SB := singular_chains Real R (subset_space B).
Let SI := singular_chains Real R (subset_space (A `&` B)).
Let SC := @small_chains Real X bool (binary_cover A B) R.
Let SM := small_subcomplex Real (binary_cover A B).
Let inc := @small_chain_inclusion Real X bool (binary_cover A B) R.

Definition left_small_le : subcomplex_le (landing_subcomplex Real A) SM.
Proof. move=> n s hs; exists true; exact hs. Defined.
Definition right_small_le : subcomplex_le (landing_subcomplex Real B) SM.
Proof. move=> n s hs; exists false; exact hs. Defined.
Definition small_left : chain_map SA SC := chain_map_of R
  (nat_comp (subspace_to_landing Real A) (subcomplex_map left_small_le)).
Definition small_right : chain_map SB SC := chain_map_of R
  (nat_comp (subspace_to_landing Real B) (subcomplex_map right_small_le)).

Lemma small_left_ambient n (a : chain_term SA n) :
  chain_map_at inc n (chain_map_at small_left n a) = chain_map_at (subspace_chain_inclusion Real A R) n a.
Proof.
apply (free_lift_ext (g := (chain_map_at inc n \o chain_map_at small_left n : {linear _ -> _}))
  (h := chain_map_at (subspace_chain_inclusion Real A R) n)).
move=> s; change (map_at R (subcomplex_inclusion SM) n
 (map_at R (nat_comp (subspace_to_landing Real A) (subcomplex_map left_small_le)) n (free_basis R s)) =
 map_at R (singular_map Real (subset_inclusion A)) n (free_basis R s)).
by rewrite !map_at_basis.
Qed.

Lemma small_right_ambient n (b : chain_term SB n) :
  chain_map_at inc n (chain_map_at small_right n b) = chain_map_at (subspace_chain_inclusion Real B R) n b.
Proof.
apply (free_lift_ext (g := (chain_map_at inc n \o chain_map_at small_right n : {linear _ -> _}))
  (h := chain_map_at (subspace_chain_inclusion Real B R) n)).
move=> s; change (map_at R (subcomplex_inclusion SM) n
 (map_at R (nat_comp (subspace_to_landing Real B) (subcomplex_map right_small_le)) n (free_basis R s)) =
 map_at R (singular_map Real (subset_inclusion B)) n (free_basis R s)).
by rewrite !map_at_basis.
Qed.

Lemma small_sum_pair n a b :
  chain_map_at (subspace_sum_small Real R A B) n (a,b) =
  chain_map_at small_left n a + chain_map_at small_right n b.
Proof.
apply: (@small_chain_inclusion_injective Real X bool (binary_cover A B) R n).
by rewrite linearD subspace_sum_small_ambient small_left_ambient small_right_ambient.
Qed.

Definition intersection_to_left : chain_map SI SA :=
  singular_chain_map Real R (intersection_left_inclusion A B).
Definition intersection_to_right : chain_map SI SB :=
  singular_chain_map Real R (intersection_right_inclusion A B).

Lemma small_intersection_square n (c : chain_term SI n) :
  chain_map_at small_left n (chain_map_at intersection_to_left n c) =
  chain_map_at small_right n (chain_map_at intersection_to_right n c).
Proof.
have h := @exact_composite R SI (binary_chains SA SB) SC
 (subspace_intersection_sum Real R A B) (subspace_sum_small Real R A B)
 (subspace_sequence_short_exact Real R A B) n c.
rewrite subspace_intersection_sum_literal in h.
change (chain_map_at (subspace_sum_small Real R A B) n
 (chain_map_at intersection_to_left n c, - chain_map_at intersection_to_right n c) = 0) in h.
rewrite small_sum_pair linearN in h.
apply/eqP; rewrite -subr_eq0; apply/eqP; exact h.
Qed.

Lemma small_sum_kernel n a b :
  chain_map_at small_left n a + chain_map_at small_right n b = 0 ->
  exists c, chain_map_at intersection_to_left n c = a /\ - chain_map_at intersection_to_right n c = b.
Proof.
rewrite -small_sum_pair => h.
case: (@exact_kernel R SI (binary_chains SA SB) SC
 (subspace_intersection_sum Real R A B) (subspace_sum_small Real R A B)
 (subspace_sequence_short_exact Real R A B) n (a,b) h) => c hc.
rewrite subspace_intersection_sum_literal in hc.
exists c; split; [exact (congr1 fst hc) | exact (congr1 snd hc)].
Qed.

Lemma small_sum_surjective n (s : chain_term SC n) :
  exists a b, chain_map_at small_left n a + chain_map_at small_right n b = s.
Proof.
case: (@exact_surjective R SI (binary_chains SA SB) SC
 (subspace_intersection_sum Real R A B) (subspace_sum_small Real R A B)
 (subspace_sequence_short_exact Real R A B) n s) => z h.
case: z h => a b h.
exists a, b; by rewrite -small_sum_pair.
Qed.

Lemma small_left_injective n : injective (chain_map_at small_left n).
Proof.
move=> a b h; apply: (@subspace_chain_inclusion_injective Real X A R n).
by rewrite -!small_left_ambient h.
Qed.
Lemma small_right_injective n : injective (chain_map_at small_right n).
Proof.
move=> a b h; apply: (@subspace_chain_inclusion_injective Real X B R n).
by rewrite -!small_right_ambient h.
Qed.
End SmallMaps.
End DPSingularExcisionSmallMaps.
