(** Actual iterated chain maps and their induced native homology maps. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps.
Local Open Scope ring_scope.

Module DPChainIteration.
Section Iteration.
Variable R : pzRingType.
Variable C : chain_complex R.
Variable s : chain_map C C.

Fixpoint chain_power k : chain_map C C :=
  match k with 0%N => chain_identity C | k.+1 => chain_composition (chain_power k) s end.

Lemma chain_power_zero n x : chain_map_at (chain_power 0) n x = x.
Proof. reflexivity. Qed.
Lemma chain_power_succ k n x : chain_map_at (chain_power k.+1) n x =
  chain_map_at s n (chain_map_at (chain_power k) n x).
Proof. reflexivity. Qed.

Theorem chain_power_homology (h : chain_homotopy s (chain_identity C)) k n
    (q : homology C n) : homology_map (chain_power k) n q = q.
Proof.
elim: k => [|k ih]; first exact: homology_map_identity.
change (homology_map (chain_composition (chain_power k) s) n q = q).
rewrite homology_map_composition ih (homology_map_homotopy h).
exact: homology_map_identity.
Qed.
End Iteration.

Section Compatibility.
Variable R : pzRingType.
Variables S C : chain_complex R.
Variable i : chain_map S C.
Variable t : chain_map S S.
Variable s : chain_map C C.
Variable w : forall n x, chain_map_at i n (chain_map_at t n x) =
  chain_map_at s n (chain_map_at i n x).

Theorem chain_power_commutes k n x :
  chain_map_at i n (chain_map_at (chain_power t k) n x) =
  chain_map_at (chain_power s k) n (chain_map_at i n x).
Proof. by elim: k => [|k ih] //; rewrite !chain_power_succ w ih. Qed.

Lemma cycle_of_injective_map (hi : forall n, injective (chain_map_at i n)) n x :
  @cycle R C n (chain_map_at i n x) -> @cycle R S n x.
Proof.
case: n x => [|n] x h; first exact I.
apply: (@hi n); rewrite linear0 -chain_map_commutes; exact h.
Qed.
End Compatibility.
End DPChainIteration.
