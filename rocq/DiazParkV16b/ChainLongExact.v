(** Full long exact sequence of native homology, including the terminal H0 epi. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainIteration ChainShortExact ChainConnecting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainIteration DPChainShortExact DPChainConnecting.
Local Open Scope ring_scope.

Module DPChainLongExact.
Section LongExact.
Variable R : pzRingType.
Variables A B C : chain_complex R.
Variables (f : chain_map A B) (g : chain_map B C).
Variable s : chain_short_exact f g.

Theorem connecting_map_kernel n (q : homology C n.+1) :
  connecting_map s n q = 0 <-> exists r, homology_map g n.+1 r = q.
Proof.
have [z <-] := quotient_pi_surjective q; rewrite connecting_map_pi; split.
- move=> hz.
  have ha : @boundary R A n (connecting_preimage s z).
    have hm := proj1 (quotient_pi_kernel _ _) hz; exact: hm.
  have [u hu] := ha.
  pose b := connecting_lift s z - chain_map_at f n.+1 u.
  have hb : @cycle R B n.+1 b.
    change (chain_d B n b = 0).
    by rewrite /b linearB chain_map_commutes hu connecting_preimage_spec subrr.
  exists (homology_class hb); rewrite homology_map_class /homology_class.
  congr (quotient_pi _ _); apply submodule_val_injective.
  change (chain_map_at g n.+1 b = val z).
  by rewrite /b linearB connecting_lift_spec (@exact_composite R A B C f g s n.+1 u) subr0.
- move=> [r hr]; have [w hw] := quotient_pi_surjective r.
  have hc : connecting_map s n (homology_map g n.+1 r) = 0.
    rewrite -hw homology_map_pi connecting_map_pi.
    have he := @connecting_class_solution R A B C f g s n (cycle_map g n.+1 w) (val w) 0.
    have hf : chain_map_at f n (val (0 : cycle_module A n)) = chain_d B n (val w).
      rewrite !linear0; symmetry; exact: (submodule_val_mem w).
    rewrite (he (Logic.eq_refl _) hf); exact: linear0.
  by rewrite hr connecting_map_pi in hc.
Qed.

Theorem connecting_map_image n (q : homology A n) :
  homology_map f n q = 0 <-> exists r, connecting_map s n r = q.
Proof.
split.
- move=> hq; have [a ha] := quotient_pi_surjective q.
  rewrite -ha homology_map_pi in hq; rewrite -ha.
  have hf : @boundary R B n (chain_map_at f n (val a)).
    have hm := proj1 (quotient_pi_kernel _ _) hq; exact: hm.
  have [b hb] := hf.
  have hz : @cycle R C n.+1 (chain_map_at g n.+1 b).
    change (chain_d C n (chain_map_at g n.+1 b) = 0).
    rewrite chain_map_commutes hb; exact: (@exact_composite R A B C f g s n).
  exists (homology_class hz); rewrite /homology_class connecting_map_pi.
  apply: (@connecting_class_solution R A B C f g s n (cycle_of_cycle hz) b a).
  + reflexivity.
  + exact: esym hb.
- move=> [r <-]; have [z <-] := quotient_pi_surjective r.
  rewrite connecting_map_pi /connecting_class homology_map_pi.
  apply/quotient_pi_kernel.
  change (exists b, chain_d B n b = chain_map_at f n (connecting_preimage s z)).
  exists (connecting_lift s z); symmetry; exact: connecting_preimage_spec.
Qed.

Lemma middle_cycle n (b : cycle_module B n) (hb : chain_map_at g n (val b) = 0) :
  exists a, homology_map f n a = quotient_pi (boundaries_in_cycles B n) b.
Proof.
have [a ha] := @exact_kernel R A B C f g s n _ hb.
have ac : @cycle R A n a.
  apply: (@cycle_of_injective_map R A B f (@exact_injective R A B C f g s) n a).
  rewrite ha; apply/cycle_subspaceE; exact: submodule_val_mem.
exists (homology_class ac); rewrite homology_map_class /homology_class.
congr (quotient_pi _ _); apply submodule_val_injective; exact: ha.
Qed.

Theorem homology_middle_exact n (q : homology B n) :
  homology_map g n q = 0 <-> exists a, homology_map f n a = q.
Proof.
split.
- move=> hq; have [b hb] := quotient_pi_surjective q.
  rewrite -hb homology_map_pi in hq; rewrite -hb.
  have gb : @boundary R C n (chain_map_at g n (val b)).
    have hm := proj1 (quotient_pi_kernel _ _) hq; exact: hm.
  have [c hc] := gb; have [t ht] := @exact_surjective R A B C f g s n.+1 c.
  pose v := val b - chain_d B n t.
  have vc : @cycle R B n v.
    apply/cycle_subspaceE; apply: subspace_sub.
    + exact: submodule_val_mem.
    + apply/cycle_subspaceE; apply: boundary_cycle; by exists t.
  have vg : chain_map_at g n v = 0.
    by rewrite /v linearB -chain_map_commutes ht hc subrr.
  have [a ha] := @middle_cycle n (cycle_of_cycle vc) vg.
  exists a; rewrite ha; apply/homology_pi_eq.
  change (exists w, chain_d B n w = v - val b).
  exists (-t); rewrite linearN /v.
  by rewrite addrAC subrr add0r.
- move=> [a <-]; have [z <-] := quotient_pi_surjective a.
  rewrite !homology_map_pi; apply/quotient_pi_kernel.
  have hz : cycle_map g n (cycle_map f n z) = 0.
    apply submodule_val_injective.
    change (chain_map_at g n (chain_map_at f n (val z)) = 0).
    exact: (@exact_composite R A B C f g s n).
  rewrite hz; exact: subspace_zero.
Qed.

Theorem homology_zero_surjective : forall q : homology C 0%N, exists r,
  homology_map g 0%N r = q.
Proof.
move=> q; have [z <-] := quotient_pi_surjective q.
have [b hb] := @exact_surjective R A B C f g s 0%N (val z).
have bc : @cycle R B 0%N b := I.
exists (homology_class bc); rewrite homology_map_class /homology_class.
congr (quotient_pi _ _); apply submodule_val_injective; exact: hb.
Qed.

Theorem long_exact_homology :
  (forall q : homology C 0%N, exists r, homology_map g 0%N r = q) /\
  forall n, linear_exact (homology_map f n) (homology_map g n) /\
    linear_exact (homology_map g n.+1) (connecting_map s n) /\
    linear_exact (connecting_map s n) (homology_map f n).
Proof.
split; first exact: homology_zero_surjective.
move=> n; split; first exact: homology_middle_exact.
split; [exact: connecting_map_kernel | exact: connecting_map_image].
Qed.
End LongExact.
End DPChainLongExact.
