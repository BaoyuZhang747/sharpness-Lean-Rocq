(** Native quasi-isomorphisms pass through exhaustive injective stages.
    The hypotheses are literal finite-chain lifts, not preservation of an
    abstract colimit or any topological pushout. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From DiazParkV16b Require Import ChainComplex ChainQuasiIsomorphism ChainMappingCone
  ChainMappingConeAcyclic ChainMappingConeReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainQuasiIsomorphism DPChainMappingCone
  DPChainMappingConeAcyclic DPChainMappingConeReflection.
Local Open Scope ring_scope.

Module DPChainExhaustiveComparison.
Section Generic.
Variable R : pzRingType.

Lemma injective_chain_map_cycle_reflect (C D : chain_complex R) (a : chain_map C D)
  (hi : forall n, injective (chain_map_at a n)) n (x : chain_term C n) :
  @cycle R D n (chain_map_at a n x) -> @cycle R C n x.
Proof.
case: n x => [|n] x; first by [].
move=> hx; apply (@hi n _ _).
rewrite linear0 -chain_map_commutes; exact hx.
Qed.

Theorem acyclic_of_exhaustive_stages (I : Type) (K : chain_complex R)
  (L : I -> chain_complex R) (a : forall i, chain_map (L i) K)
  (hi : forall i n, injective (chain_map_at (a i) n))
  (hcover : forall n (x : chain_term K n), exists i y, chain_map_at (a i) n y = x)
  (hL : forall i, acyclic (L i)) : acyclic K.
Proof.
move=> n x hx; have [i [y hy]] := hcover n x.
have hcy : @cycle R (L i) n y.
  apply (@injective_chain_map_cycle_reflect (L i) K (a i) (@hi i) n y).
  by rewrite hy.
have [w hw] := @hL i n y hcy.
exists (chain_map_at (a i) n.+1 w).
by rewrite chain_map_commutes hw hy.
Qed.

Section ConeMap.
Variables C D C' D' : chain_complex R.
Variables (f : chain_map C D) (f' : chain_map C' D').
Variables (a : chain_map C' C) (b : chain_map D' D).
Variable w : forall n x, chain_map_at b n (chain_map_at f' n x) =
  chain_map_at f n (chain_map_at a n x).

Definition cone_map_function n : chain_term (mapping_cone f') n ->
    chain_term (mapping_cone f) n :=
  match n as k return chain_term (mapping_cone f') k -> chain_term (mapping_cone f) k with
  | 0%N => chain_map_at b 0%N
  | k.+1 => fun z => (chain_map_at b k.+1 z.1, chain_map_at a k z.2)
  end.

Lemma cone_map_linear n : linear (@cone_map_function n).
Proof.
case: n => [|n]; first exact: linearP.
move=> r [y x] [y' x']; change
  ((chain_map_at b n.+1 (r *: y + y'), chain_map_at a n (r *: x + x')) =
   (r *: chain_map_at b n.+1 y + chain_map_at b n.+1 y',
    r *: chain_map_at a n x + chain_map_at a n x')).
by rewrite !linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (@cone_map_function n) (@cone_map_linear n).

Definition cone_map : chain_map (mapping_cone f') (mapping_cone f).
Proof.
refine (@ChainMap R _ _ (fun n => (@cone_map_function n : {linear _ -> _})) _).
case=> [|n] [y x].
- change (chain_d D 0%N (chain_map_at b 1%N y) +
    chain_map_at f 0%N (chain_map_at a 0%N x) =
    chain_map_at b 0%N (chain_d D' 0%N y + chain_map_at f' 0%N x)).
  by rewrite linearD chain_map_commutes w.
- change ((chain_d D n.+1 (chain_map_at b n.+2 y) +
    chain_map_at f n.+1 (chain_map_at a n.+1 x), -chain_d C n (chain_map_at a n.+1 x)) =
    (chain_map_at b n.+1 (chain_d D' n.+1 y + chain_map_at f' n.+1 x),
      chain_map_at a n (-chain_d C' n x))).
  by rewrite linearD linearN !chain_map_commutes w.
Defined.

Lemma cone_map_injective (ha : forall n, injective (chain_map_at a n))
  (hb : forall n, injective (chain_map_at b n)) n : injective (chain_map_at cone_map n).
Proof.
case: n => [|n]; first exact: hb.
move=> [y x] [y' x'] he.
have ey : y = y' := @hb n.+1 y y' (congr1 (@fst _ _) he).
have ex : x = x' := @ha n x x' (congr1 (@snd _ _) he).
by rewrite ey ex.
Qed.
End ConeMap.

Theorem quasi_iso_of_exhaustive_stages (I : Type) (C D : chain_complex R)
  (f : chain_map C D) (C' D' : I -> chain_complex R)
  (f' : forall i, chain_map (C' i) (D' i))
  (a : forall i, chain_map (C' i) C) (b : forall i, chain_map (D' i) D)
  (ha : forall i n, injective (chain_map_at (a i) n))
  (hb : forall i n, injective (chain_map_at (b i) n))
  (w : forall i n x, chain_map_at (b i) n (chain_map_at (f' i) n x) =
    chain_map_at f n (chain_map_at (a i) n x))
  (hzero : forall y : chain_term D 0%N, exists i y', chain_map_at (b i) 0%N y' = y)
  (hpair : forall n (y : chain_term D n.+1) (x : chain_term C n),
    exists i y' x', chain_map_at (b i) n.+1 y' = y /\ chain_map_at (a i) n x' = x)
  (hstage : forall i, quasi_isomorphism (f' i)) : quasi_isomorphism f.
Proof.
apply: mapping_cone_acyclic_reflects.
apply: (@acyclic_of_exhaustive_stages I (mapping_cone f)
  (fun i => mapping_cone (f' i))
  (fun i => @cone_map C D (C' i) (D' i) f (f' i) (a i) (b i) (@w i))).
- move=> i n; exact (@cone_map_injective C D (C' i) (D' i)
    f (f' i) (a i) (b i) (@w i) (@ha i) (@hb i) n).
- case=> [y|n [y x]].
  + have [i [y' hy]] := hzero y; exists i,y'; exact hy.
  + have [i [y' [x' [hy hx]]]] := hpair n y x.
    exists i,(y',x'); change ((chain_map_at (b i) n.+1 y',chain_map_at (a i) n x')=(y,x)).
    by rewrite hy hx.
- move=> i; exact: mapping_cone_acyclic (hstage i).
Qed.
End Generic.
End DPChainExhaustiveComparison.
