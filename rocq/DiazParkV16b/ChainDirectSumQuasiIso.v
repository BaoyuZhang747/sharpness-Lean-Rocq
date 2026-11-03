(** Arbitrary actual direct sums preserve actual chain quasi-isomorphisms.
    Lifts use only the finite support of each requested chain. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModuleDirectSums MackeyModuleCarriers.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainQuasiIsomorphism ChainQuasiIsoCriterion ChainDirectSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainQuasiIsomorphism DPChainQuasiIsoCriterion DPChainDirectSum.
Local Open Scope ring_scope.
Module DPChainDirectSumQuasiIso.
Section Comparison.
Variable R : pzRingType.
Variable I : Type.
Variables C D : I -> chain_complex R.
Variable f : forall i, chain_map (C i) (D i).
Variable hf : forall i, quasi_isomorphism (f i).

Lemma direct_sum_boundary_reflect n (x : chain_term (direct_sum C) n)
    (hx : @cycle R (direct_sum C) n x) :
  @boundary R (direct_sum D) n (chain_map_at (direct_sum_map f) n x) ->
    @boundary R (direct_sum C) n x.
Proof.
move=> hb; apply/direct_sum_boundary => i.
apply: (@quasi_iso_boundary_reflect R (C i) (D i) (f i) (hf i) n).
- exact: (proj1 (direct_sum_cycle x) hx i).
- exact: (proj1 (direct_sum_boundary _) hb i).
Qed.

Lemma direct_sum_cycle_lift n (y : chain_term (direct_sum D) n)
    (hy : @cycle R (direct_sum D) n y) :
  exists x : chain_term (direct_sum C) n, exists hx : @cycle R (direct_sum C) n x,
    exists w : chain_term (direct_sum D) n.+1,
      chain_d (direct_sum D) n w + chain_map_at (direct_sum_map f) n x = y.
Proof.
have hp i : exists z : (cycle_module (C i) n * chain_term (D i) n.+1)%type,
    chain_d (D i) n z.2 + chain_map_at (f i) n (val z.1) = sum_coefficient y i.
  have hiy := proj1 (direct_sum_cycle y) hy i.
  have [x [hx [w hw]]] := @quasi_iso_cycle_lift R (C i) (D i) (f i) (hf i) n _ hiy.
  exists (cycle_of_cycle hx,w); exact hw.
pose z i := proj1_sig (constructive_indefinite_description (hp i)).
have hz i : chain_d (D i) n (z i).2 + chain_map_at (f i) n (val (z i).1) = sum_coefficient y i.
  exact: (proj2_sig (constructive_indefinite_description (hp i))).
pose c : cycle_module (direct_sum C) n :=
  \sum_(i <- sum_support y) cycle_map (direct_sum_inclusion C i) n (z i).1.
pose x := cycle_inclusion (direct_sum C) n c.
have hx : @cycle R (direct_sum C) n x.
  apply/cycle_subspaceE; exact: submodule_val_mem.
pose w : chain_term (direct_sum D) n.+1 := \sum_(i <- sum_support y)
  @sum_single R I (fun j => chain_term (D j) n.+1) i (z i).2.
exists x, hx, w.
have ex : x = \sum_(i <- sum_support y)
    @sum_single R I (fun j => chain_term (C j) n) i (val (z i).1).
  rewrite /x /c linear_sum.
  apply: eq_bigr => i _; reflexivity.
rewrite ex /w !linear_sum -big_split -[RHS](sum_generation y).
apply: eq_bigr => i _.
rewrite direct_sum_d_single direct_sum_map_single.
change (@sum_single R I (fun j => chain_term (D j) n) i
    (chain_d (D i) n (z i).2) +
  @sum_single R I (fun j => chain_term (D j) n) i
    (chain_map_at (f i) n (val (z i).1)) = sum_single (sum_coefficient y i)).
by rewrite -linearD hz.
Qed.

Theorem direct_sum_quasi_isomorphism : quasi_isomorphism (direct_sum_map f).
Proof.
apply: quasi_isomorphism_of_cycle_lift.
- exact: direct_sum_boundary_reflect.
- exact: direct_sum_cycle_lift.
Qed.
End Comparison.
End DPChainDirectSumQuasiIso.
