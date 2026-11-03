(** Representative lifting and boundary reflection certify the literal native homology map. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainQuasiIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism.
Local Open Scope ring_scope.
Module DPChainQuasiIsoCriterion.
Section Criterion.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Variable hreflect : forall n (x : chain_term C n), @cycle R C n x ->
  @boundary R D n (chain_map_at f n x) -> @boundary R C n x.
Variable hlift : forall n (y : chain_term D n), @cycle R D n y ->
  exists x : chain_term C n, exists hx : @cycle R C n x,
    exists w : chain_term D n.+1, chain_d D n w + chain_map_at f n x = y.

Lemma criterion_kernel_zero n (q : homology C n) : homology_map f n q = 0 -> q = 0.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite homology_map_pi=> hq.
have hb := proj1 (quotient_pi_kernel _ _) hq.
change (@boundary R D n (chain_map_at f n (val z))) in hb.
apply/quotient_pi_kernel; change (@boundary R C n (val z)).
apply: hreflect hb.
apply/cycle_subspaceE; exact: submodule_val_mem.
Qed.
Lemma criterion_injective n : injective (homology_map f n).
Proof.
move=> x y h; apply/subr0_eq; apply: criterion_kernel_zero.
by rewrite linearB h subrr.
Qed.
Lemma criterion_surjective n : forall q : homology D n, exists r, homology_map f n r = q.
Proof.
move=> q; have [z <-] := quotient_pi_surjective q.
have hz : @cycle R D n (val z) := proj1 (@cycle_subspaceE R D n _) (submodule_val_mem z).
have [x [hx [w hw]]] := hlift hz.
exists (homology_class hx); rewrite /homology_class homology_map_pi.
apply/homology_pi_eq; change (@boundary R D n (chain_map_at f n x - val z)).
exists (-w); rewrite linearN -hw.
by rewrite opprD addrCA subrr addr0.
Qed.
Theorem quasi_isomorphism_of_cycle_lift : quasi_isomorphism f.
Proof. move=> n; split; [exact: criterion_injective | exact: criterion_surjective]. Qed.
End Criterion.
End DPChainQuasiIsoCriterion.
