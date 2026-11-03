(** The actual nonnegative mapping cone, with differential (d y + f x,-d x). *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From DiazParkV16b Require Import ChainComplex LinearProjective.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPLinearProjective.
Local Open Scope ring_scope.

Module DPChainMappingCone.
Section Cone.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Definition cone_term n : lmodType R :=
  match n with
  | 0%N => chain_term D 0%N
  | k.+1 => [the lmodType R of (chain_term D k.+1 * chain_term C k)%type]
  end.
Definition cone_d n : cone_term n.+1 -> cone_term n :=
  match n as k return cone_term k.+1 -> cone_term k with
  | 0%N => fun x => chain_d D 0%N x.1 + chain_map_at f 0%N x.2
  | k.+1 => fun x => (chain_d D k.+1 x.1 + chain_map_at f k.+1 x.2, - chain_d C k x.2)
  end.
Arguments cone_d n x : clear implicits.
Lemma cone_d_linear n : linear (cone_d n).
Proof.
case: n => [|n]; move=> r [a b] [c d].
- change (chain_d D 0%N (r *: a+c) + chain_map_at f 0%N (r *: b+d) =
    r *: (chain_d D 0%N a + chain_map_at f 0%N b) + (chain_d D 0%N c + chain_map_at f 0%N d)).
  by rewrite !linearP scalerDr addrACA.
- change ((chain_d D n.+1 (r *: a+c) + chain_map_at f n.+1 (r *: b+d), -chain_d C n (r *: b+d)) =
    (r *: (chain_d D n.+1 a + chain_map_at f n.+1 b) + (chain_d D n.+1 c + chain_map_at f n.+1 d),
     r *: (-chain_d C n b) + (-chain_d C n d))).
  congr (_, _); first by rewrite !linearP scalerDr addrACA.
  by rewrite linearP opprD scalerN.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (cone_d n) (@cone_d_linear n).
Lemma cone_d_squared n (x : cone_term n.+2) : cone_d n (cone_d n.+1 x) = 0.
Proof.
case: n x => [|n] [y x].
- change (chain_d D 0%N (chain_d D 1%N y + chain_map_at f 1%N x) + chain_map_at f 0%N (-chain_d C 0%N x) = 0).
  by rewrite linearD chain_d2 chain_map_commutes linearN add0r subrr.
- change ((chain_d D n.+1 (chain_d D n.+2 y + chain_map_at f n.+2 x) + chain_map_at f n.+1 (-chain_d C n.+1 x),
    -chain_d C n (-chain_d C n.+1 x)) = (0,0)).
  congr (_, _).
  + by rewrite linearD chain_d2 chain_map_commutes linearN add0r subrr.
  + by rewrite linearN chain_d2 /= !oppr0.
Qed.
Definition mapping_cone : chain_complex R :=
  @ChainComplex R cone_term (fun n => (cone_d n : {linear _ -> _})) cone_d_squared.
Definition cone_inclusion_at n : {linear chain_term D n -> cone_term n} :=
  match n as k return {linear chain_term D k -> cone_term k} with
  | 0%N => idfun
  | k.+1 => @product_left R (chain_term D k.+1) (chain_term C k)
  end.
Definition cone_inclusion : chain_map D mapping_cone.
Proof.
refine (@ChainMap R D mapping_cone cone_inclusion_at _).
case=> [|n] x.
- change (chain_d D 0%N x + chain_map_at f 0%N 0 = chain_d D 0%N x); by rewrite linear0 addr0.
- change ((chain_d D n.+1 x + chain_map_at f n.+1 0, -chain_d C n 0) = (chain_d D n.+1 x,0)).
  by rewrite !linear0 addr0 /=.
Defined.
Lemma mapping_cone_projective
    (hC : forall n, linear_projective (chain_term C n))
    (hD : forall n, linear_projective (chain_term D n)) n :
  linear_projective (chain_term mapping_cone n).
Proof.
case: n => [|n]; first exact: hD.
apply product_projective; [exact: hD | exact: hC].
Qed.
End Cone.
End DPChainMappingCone.
