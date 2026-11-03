(** Actual commuting chain-map squares induce literal native homology squares. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainHomology DPChainHomologyMaps.
Module DPChainHomologySquares.
Section Squares.
Variable R : pzRingType.
Variables A B A' B' : chain_complex R.
Variables (f : chain_map A B) (u : chain_map A A') (v : chain_map B B') (f' : chain_map A' B').
Variable h : forall n x, chain_map_at v n (chain_map_at f n x) =
  chain_map_at f' n (chain_map_at u n x).

Theorem homology_square n (q : homology A n) :
  homology_map v n (homology_map f n q) = homology_map f' n (homology_map u n q).
Proof.
have [z <-] := quotient_pi_surjective q; rewrite !homology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective.
exact: h.
Qed.
End Squares.
End DPChainHomologySquares.
