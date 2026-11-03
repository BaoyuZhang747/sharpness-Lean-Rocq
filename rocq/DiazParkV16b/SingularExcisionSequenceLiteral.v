(** The transported sequence has the literal ambient inclusion sum as its second map. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialSubcomplex
  SimplicialChains SimplicialChainsMaps SingularSet SingularCohomology SingularSmallChains
  SingularChainExcisionSubspaces SingularChainExcisionSubspacesLattice
  SingularChainExcisionSubspacesExact SingularExcisionSequenceMaps SingularExcisionSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialSet DPSimplicialSubcomplex
  DPSimplicialChains DPSimplicialChainMaps DPSingularSet DPSingularCohomology DPSingularSmallChains
  DPSingularChainExcisionSubspaces DPSingularChainExcisionSubspacesLattice
  DPSingularChainExcisionSubspacesExact DPSingularExcisionSequenceMaps DPSingularExcisionSequence.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularExcisionSequenceLiteral.
Section Literal.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variables A B : set X.
Let LA := landing_subcomplex Real A.
Let LB := landing_subcomplex Real B.
Let LU := subcomplex_union LA LB.
Let SC := @small_chains Real X bool (binary_cover A B) R.
Let inc := @small_chain_inclusion Real X bool (binary_cover A B) R.
Let GU := chains R (subcomplex_set LU).
Let uinc := chain_map_of R (subcomplex_inclusion LU).

Lemma union_from_ambient n (x : chain_term GU n) :
  chain_map_at inc n (chain_map_at (union_from Real R A B) n x) =
  chain_map_at uinc n x.
Proof.
apply (free_lift_ext (g := (chain_map_at inc n \o chain_map_at (union_from Real R A B) n : {linear _ -> _}))
  (h := chain_map_at uinc n)).
move=> s; change (map_at R (subcomplex_inclusion (small_subcomplex Real (binary_cover A B))) n
  (map_at R (subcomplex_map (@small_union_from Real X A B)) n (free_basis R s)) =
  map_at R (subcomplex_inclusion LU) n (free_basis R s)).
by rewrite !map_at_basis.
Qed.

Lemma union_left_ambient n (x : chain_term (landing_chains Real A R) n) :
  chain_map_at uinc n (chain_map_at (union_left R LA LB) n x) =
  chain_map_at (landing_chain_inclusion Real A R) n x.
Proof.
apply (free_lift_ext (g := (chain_map_at uinc n \o chain_map_at (union_left R LA LB) n : {linear _ -> _}))
  (h := chain_map_at (landing_chain_inclusion Real A R) n)).
move=> s; change (map_at R (subcomplex_inclusion LU) n
 (map_at R (subcomplex_map (fun n s (h : member LA n s) => (or_introl h : member LU n s))) n (free_basis R s)) =
 map_at R (subcomplex_inclusion LA) n (free_basis R s)).
by rewrite !map_at_basis.
Qed.

Lemma union_right_ambient n (x : chain_term (landing_chains Real B R) n) :
  chain_map_at uinc n (chain_map_at (union_right R LA LB) n x) =
  chain_map_at (landing_chain_inclusion Real B R) n x.
Proof.
apply (free_lift_ext (g := (chain_map_at uinc n \o chain_map_at (union_right R LA LB) n : {linear _ -> _}))
  (h := chain_map_at (landing_chain_inclusion Real B R) n)).
move=> s; change (map_at R (subcomplex_inclusion LU) n
 (map_at R (subcomplex_map (fun n s (h : member LB n s) => (or_intror h : member LU n s))) n (free_basis R s)) =
 map_at R (subcomplex_inclusion LB) n (free_basis R s)).
by rewrite !map_at_basis.
Qed.

Theorem subspace_sum_small_ambient n
    (a : chain_term (singular_chains Real R (subset_space A)) n)
    (b : chain_term (singular_chains Real R (subset_space B)) n) :
  chain_map_at inc n (chain_map_at (subspace_sum_small Real R A B) n (a,b)) =
  chain_map_at (subspace_chain_inclusion Real A R) n a +
  chain_map_at (subspace_chain_inclusion Real B R) n b.
Proof.
rewrite subspace_sum_small_at union_from_ambient.
change (chain_map_at uinc n
 (chain_map_at (union_left R LA LB) n (chain_map_at (subspace_to_landing_chains Real A R) n a) +
 chain_map_at (union_right R LA LB) n (chain_map_at (subspace_to_landing_chains Real B R) n b)) =
 chain_map_at (subspace_chain_inclusion Real A R) n a +
 chain_map_at (subspace_chain_inclusion Real B R) n b).
by rewrite linearD union_left_ambient union_right_ambient !subspace_to_landing_chain_inclusion.
Qed.

End Literal.
End DPSingularExcisionSequenceLiteral.
