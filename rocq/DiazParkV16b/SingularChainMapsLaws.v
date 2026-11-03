(** Literal functor laws for the constructed singular chain maps. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import TopologicalCategory SingularSet SingularCohomology
  SimplicialChains SimplicialChainsMaps ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPTopological DPSingularSet DPSingularCohomology
  DPSimplicialChains DPSimplicialChainMaps DPChainComplex.

Module DPSingularChainMapsLaws.
Section Laws.
Variable Real : realType.
Variable R : pzRingType.

Lemma singular_chain_identity (X : topologicalType) n
    (x : chain_term (singular_chains Real R X) n) :
  chain_map_at (singular_chain_map Real R (continuous_identity X)) n x = x.
Proof.
apply: (free_lift_ext (g := chain_map_at (singular_chain_map Real R (continuous_identity X)) n)
  (h := (idfun : {linear _ -> _}))).
move=> s; change (map_at R (singular_map Real (continuous_identity X)) n (free_basis R s) = free_basis R s).
by rewrite map_at_basis singular_map_identity.
Qed.

Lemma singular_chain_composition (X Y Z : topologicalType)
    (f : hom topological_category X Y) (g : hom topological_category Y Z) n
    (x : chain_term (singular_chains Real R X) n) :
  chain_map_at (singular_chain_map Real R (compose f g)) n x =
  chain_map_at (singular_chain_map Real R g) n
    (chain_map_at (singular_chain_map Real R f) n x).
Proof.
apply: (free_lift_ext
  (g := chain_map_at (singular_chain_map Real R (compose f g)) n)
  (h := (chain_map_at (singular_chain_map Real R g) n \o
    chain_map_at (singular_chain_map Real R f) n : {linear _ -> _}))).
move=> s; change (map_at R (singular_map Real (compose f g)) n (free_basis R s) =
  map_at R (singular_map Real g) n (map_at R (singular_map Real f) n (free_basis R s))).
by rewrite !map_at_basis singular_map_composition.
Qed.
End Laws.
End DPSingularChainMapsLaws.
