(** Acyclicity of the actual nonnegative mapping cone reflects a genuine
    homology-bijective chain map, including degree zero. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainQuasiIsomorphism ChainMappingCone ChainMappingConeAcyclic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainQuasiIsomorphism DPChainMappingCone DPChainMappingConeAcyclic.
Local Open Scope ring_scope.

Module DPChainMappingConeReflection.
Section Reflection.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Hypothesis hc : acyclic (mapping_cone f).

Lemma cone_cycle_lift n (y : chain_term D n) (hy : @cycle R D n y) :
  exists x : chain_term C n, exists hx : @cycle R C n x,
    exists w : chain_term D n.+1, chain_d D n w + chain_map_at f n x = y.
Proof.
have hi := @chain_map_cycle R D (mapping_cone f) (cone_inclusion f) n y hy.
have [z hz] := @hc n _ hi.
case: n y hy hi z hz => [|n] y hy hi [w x] hz.
- exists x, I, w; exact hz.
- have hx : @cycle R C n.+1 x.
    have he := congr1 (@snd (chain_term D n.+1) (chain_term C n)) hz.
    change (-chain_d C n x = 0) in he.
    apply: oppr_inj; by rewrite he oppr0.
  exists x, hx, w.
  exact (congr1 (@fst (chain_term D n.+1) (chain_term C n)) hz).
Qed.

Lemma cone_boundary_reflect n (x : chain_term C n) (hx : @cycle R C n x) :
  @boundary R D n (chain_map_at f n x) -> @boundary R C n x.
Proof.
move=> [y hy].
have hz : @cycle R (mapping_cone f) n.+1 (-y,x).
  case: n x hx y hy => [|n] x hx y hy.
  - change (chain_d D 0%N (-y) + chain_map_at f 0%N x = 0).
    by rewrite linearN hy addNr.
  - change ((chain_d D n.+1 (-y) + chain_map_at f n.+1 x, -chain_d C n x) = (0,0)).
    by rewrite linearN hy hx addNr oppr0.
have [[w z] he] := @hc n.+1 _ hz.
exists (-z); rewrite linearN.
exact (congr1 (@snd (chain_term D n.+1) (chain_term C n)) he).
Qed.

Lemma cone_homology_kernel_zero n (q : homology C n) :
  homology_map f n q = 0 -> q = 0.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite homology_map_pi=> hq.
have hb := proj1 (quotient_pi_kernel _ _) hq.
change (@boundary R D n (chain_map_at f n (val z))) in hb.
apply/quotient_pi_kernel.
change (@boundary R C n (val z)).
apply: cone_boundary_reflect hb.
apply/cycle_subspaceE; exact: submodule_val_mem.
Qed.

Lemma cone_homology_injective n : injective (homology_map f n).
Proof.
move=> x y h; apply/subr0_eq; apply: cone_homology_kernel_zero.
by rewrite linearB h subrr.
Qed.

Lemma cone_homology_surjective n : forall q : homology D n,
  exists r, homology_map f n r = q.
Proof.
move=> q; have [z <-] := quotient_pi_surjective q.
have hz : @cycle R D n (val z) := proj1 (@cycle_subspaceE R D n _) (submodule_val_mem z).
have [x [hx [w hw]]] := cone_cycle_lift hz.
exists (homology_class hx); rewrite /homology_class homology_map_pi.
apply/homology_pi_eq.
change (@boundary R D n (chain_map_at f n x - val z)).
exists (-w); rewrite linearN -hw.
by rewrite opprD addrCA subrr addr0.
Qed.

Theorem mapping_cone_acyclic_reflects : quasi_isomorphism f.
Proof. move=> n; split; [exact: cone_homology_injective | exact: cone_homology_surjective]. Qed.

End Reflection.

Theorem mapping_cone_acyclic_iff (R : pzRingType) (C D : chain_complex R)
    (f : chain_map C D) : acyclic (mapping_cone f) <-> quasi_isomorphism f.
Proof.
split; [exact: mapping_cone_acyclic_reflects | exact: mapping_cone_acyclic].
Qed.
End DPChainMappingConeReflection.
