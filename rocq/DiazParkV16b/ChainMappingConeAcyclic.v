(** A homology-bijective chain map has an acyclic actual mapping cone. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainQuasiIsomorphism ChainMappingCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainQuasiIsomorphism DPChainMappingCone.
Local Open Scope ring_scope.

Module DPChainMappingConeAcyclic.
Section Cone.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Variable hf : quasi_isomorphism f.

Theorem mapping_cone_acyclic : acyclic (mapping_cone f).
Proof.
move=> n; case: n => [|n].
- move=> y _.
  have [x [hx [w hw]]] := @quasi_iso_cycle_lift R C D f hf 0%N y I.
  exists (w,x); exact hw.
- move=> [y x] h.
  have hsum : chain_d D n y + chain_map_at f n x = 0.
    case: n y x h => [|n] y x h; first exact h.
    exact (congr1 (@fst (chain_term D n.+1) (chain_term C n)) h).
  have hx : @cycle R C n x.
    case: n y x h hsum => [|n] y x h hs; first exact I.
    have e := congr1 (@snd (chain_term D n.+1) (chain_term C n)) h.
    change (-chain_d C n x = 0) in e.
    apply: oppr_inj; by rewrite e oppr0.
  have hb : @boundary R D n (chain_map_at f n x).
    exists (-y); rewrite linearN.
    have e := congr1 (fun z => z - chain_d D n y) hsum.
    by rewrite addrAC subrr add0r sub0r in e.
  have [c hc] := @quasi_iso_boundary_reflect R C D f hf n x hx hb.
  have hz : @cycle R D n.+1 (y + chain_map_at f n.+1 c).
    change (chain_d D n (y + chain_map_at f n.+1 c) = 0).
    by rewrite linearD chain_map_commutes hc.
  have [b [hbcycle [w hw]]] := @quasi_iso_cycle_lift R C D f hf n.+1 _ hz.
  exists (w,b-c).
  change ((chain_d D n.+1 w + chain_map_at f n.+1 (b-c), -chain_d C n (b-c)) = (y,x)).
  congr (_, _).
  + by rewrite linearB addrA hw addrK.
  + change (chain_d C n b = 0) in hbcycle.
    by rewrite linearB hbcycle hc sub0r opprK.
Qed.
End Cone.
End DPChainMappingConeAcyclic.
