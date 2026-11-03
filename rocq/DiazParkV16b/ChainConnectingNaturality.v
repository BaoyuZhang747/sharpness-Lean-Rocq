(** Naturality of the actual native homology connecting map. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainShortExact ChainConnecting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainShortExact DPChainConnecting.
Local Open Scope ring_scope.

Module DPChainConnectingNaturality.
Section Naturality.
Variable R : pzRingType.
Variables A B C A' B' C' : chain_complex R.
Variables (f : chain_map A B) (g : chain_map B C)
  (f' : chain_map A' B') (g' : chain_map B' C').
Variables (s : chain_short_exact f g) (s' : chain_short_exact f' g').
Variables (u : chain_map A A') (v : chain_map B B') (w : chain_map C C').
Variable hleft : forall n x, chain_map_at v n (chain_map_at f n x) =
  chain_map_at f' n (chain_map_at u n x).
Variable hright : forall n x, chain_map_at w n (chain_map_at g n x) =
  chain_map_at g' n (chain_map_at v n x).

Theorem connecting_natural n (q : homology C n.+1) :
  connecting_map s' n (homology_map w n.+1 q) =
  homology_map u n (connecting_map s n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite homology_map_pi !connecting_map_pi /connecting_class homology_map_pi.
apply: (@connecting_class_solution R A' B' C' f' g' s' n
  (cycle_map w n.+1 z) (chain_map_at v n.+1 (connecting_lift s z))
  (cycle_map u n (connecting_cycle s z))).
- change (chain_map_at g' n.+1 (chain_map_at v n.+1 (connecting_lift s z)) =
    chain_map_at w n.+1 (val z)).
  by rewrite -hright connecting_lift_spec.
- change (chain_map_at f' n (chain_map_at u n (connecting_preimage s z)) =
    chain_d B' n (chain_map_at v n.+1 (connecting_lift s z))).
  by rewrite -hleft connecting_preimage_spec chain_map_commutes.
Qed.
End Naturality.
End DPChainConnectingNaturality.
