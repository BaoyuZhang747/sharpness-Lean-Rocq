(** An actual contraction of the mapping cone gives both homotopies for f. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From DiazParkV16b Require Import ChainComplex ChainMappingCone LinearProjective.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainMappingCone DPLinearProjective.
Local Open Scope ring_scope.

Module DPChainConeHomotopyInverse.
Section Identities.
Variable V : zmodType.
Lemma negate_sum_eq (a b c : V) : a+b=c -> -a=b-c.
Proof. move=> <-; by rewrite opprD addrCA subrr addr0. Qed.
Lemma negate_outer_sum_eq (a b c d : V) : a+b+c=d -> -a-c=b-d.
Proof.
move=> e; have e' : (a+c)+b=d by rewrite addrAC.
have h := negate_sum_eq e'; by rewrite opprD in h.
Qed.
Lemma positive_outer_sum_eq (a b c d : V) : -a+(b-c)=d -> a+c=b-d.
Proof.
move=> e; have e' : (-a-c)+b=d by rewrite addrAC -addrA.
have h := negate_sum_eq e'; by rewrite opprD !opprK in h.
Qed.
End Identities.
Section Inverse.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Let K := mapping_cone f.
Variable h : forall n, {linear chain_term K n -> chain_term K n.+1}.
Variable h0 : forall x, chain_d K 0%N (h 0%N x) = x.
Variable hS : forall n x, chain_d K n.+1 (h n.+1 x) + h n (chain_d K n x) = x.

Definition inverse_at n (x : chain_term D n) : chain_term C n :=
  (h n (@cone_inclusion_at R C D n x)).2.
Arguments inverse_at n x : clear implicits.
Lemma inverse_at_linear n : linear (inverse_at n).
Proof.
move=> r x y; rewrite /inverse_at !linearP.
reflexivity.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (inverse_at n) (@inverse_at_linear n).

Lemma inverse_at_commutes n x :
  chain_d C n (inverse_at n.+1 x) = inverse_at n (chain_d D n x).
Proof.
have e := congr1 (@snd (chain_term D n.+1) (chain_term C n))
  (@hS n (@cone_inclusion_at R C D n.+1 x)).
change (-chain_d C n (inverse_at n.+1 x) +
  (h n (chain_d K n (@cone_inclusion_at R C D n.+1 x))).2 = 0) in e.
have ec := @chain_map_commutes R D K (cone_inclusion f) n x.
change (chain_d K n (@cone_inclusion_at R C D n.+1 x) = @cone_inclusion_at R C D n (chain_d D n x)) in ec.
rewrite ec in e.
change (-chain_d C n (inverse_at n.+1 x) + inverse_at n (chain_d D n x) = 0) in e.
have ee := congr1 (fun z => chain_d C n (inverse_at n.+1 x) + z) e.
by rewrite addrA addrN add0r addr0 in ee.
Qed.
Definition inverse_chain : chain_map D C :=
  @ChainMap R D C (fun n => (inverse_at n : {linear _ -> _})) inverse_at_commutes.

Definition target_homotopy_at n (x : chain_term D n) : chain_term D n.+1 :=
  - (h n (@cone_inclusion_at R C D n x)).1.
Arguments target_homotopy_at n x : clear implicits.
Lemma target_homotopy_linear n : linear (target_homotopy_at n).
Proof.
move=> r x y; rewrite /target_homotopy_at !linearP.
by rewrite /= scalerN.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (target_homotopy_at n) (@target_homotopy_linear n).

Definition source_homotopy_at n (x : chain_term C n) : chain_term C n.+1 :=
  (h n.+1 (0,x)).2.
Arguments source_homotopy_at n x : clear implicits.
Lemma source_homotopy_linear n : linear (source_homotopy_at n).
Proof.
move=> r x y.
change ((h n.+1 (@product_right R (chain_term D n.+1) (chain_term C n) (r *: x+y))).2 =
  r *: (h n.+1 (@product_right R (chain_term D n.+1) (chain_term C n) x)).2 +
  (h n.+1 (@product_right R (chain_term D n.+1) (chain_term C n) y)).2).
rewrite !linearP; reflexivity.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (source_homotopy_at n) (@source_homotopy_linear n).

Lemma target_homotopy_zero x :
  chain_d D 0%N (target_homotopy_at 0%N x) = chain_map_at f 0%N (inverse_at 0%N x) - x.
Proof.
have e := h0 x.
change (chain_d D 0%N (h 0%N x).1 + chain_map_at f 0%N (h 0%N x).2 = x) in e.
change (chain_d D 0%N (-(h 0%N x).1) = chain_map_at f 0%N (h 0%N x).2 - x).
rewrite linearN; exact: negate_sum_eq e.
Qed.

Lemma target_homotopy_succ n x :
  chain_d D n.+1 (target_homotopy_at n.+1 x) + target_homotopy_at n (chain_d D n x) =
    chain_map_at f n.+1 (inverse_at n.+1 x) - x.
Proof.
have e := congr1 (@fst (chain_term D n.+1) (chain_term C n))
  (@hS n (@cone_inclusion_at R C D n.+1 x)).
have ec := @chain_map_commutes R D K (cone_inclusion f) n x.
change (chain_d K n (@cone_inclusion_at R C D n.+1 x) = @cone_inclusion_at R C D n (chain_d D n x)) in ec.
change (chain_d D n.+1 (h n.+1 (@cone_inclusion_at R C D n.+1 x)).1 +
  chain_map_at f n.+1 (inverse_at n.+1 x) + (h n (chain_d K n (@cone_inclusion_at R C D n.+1 x))).1 = x) in e.
rewrite ec in e.
rewrite /target_homotopy_at linearN.
exact: negate_outer_sum_eq e.
Qed.

Lemma source_homotopy_zero x :
  chain_d C 0%N (source_homotopy_at 0%N x) = inverse_at 0%N (chain_map_at f 0%N x) - x.
Proof.
have e := congr1 (@snd (chain_term D 1%N) (chain_term C 0%N)) (@hS 0%N (0,x)).
change (-chain_d C 0%N (source_homotopy_at 0%N x) + (h 0%N (chain_d D 0%N 0 + chain_map_at f 0%N x)).2 = x) in e.
rewrite linear0 add0r in e.
change (-chain_d C 0%N (source_homotopy_at 0%N x) + inverse_at 0%N (chain_map_at f 0%N x) = x) in e.
have ee := negate_sum_eq e; by rewrite opprK in ee.
Qed.

Lemma source_homotopy_succ n x :
  chain_d C n.+1 (source_homotopy_at n.+1 x) + source_homotopy_at n (chain_d C n x) =
    inverse_at n.+1 (chain_map_at f n.+1 x) - x.
Proof.
have e := congr1 (@snd (chain_term D n.+2) (chain_term C n.+1)) (@hS n.+1 (0,x)).
change (-chain_d C n.+1 (source_homotopy_at n.+1 x) +
  (h n.+1 (chain_d D n.+1 0 + chain_map_at f n.+1 x, -chain_d C n x)).2 = x) in e.
rewrite linear0 add0r in e.
have split : (chain_map_at f n.+1 x, -chain_d C n x) =
  (@cone_inclusion_at R C D n.+1 (chain_map_at f n.+1 x) - (0,chain_d C n x) : chain_term K n.+1).
  change ((chain_map_at f n.+1 x, -chain_d C n x) = (chain_map_at f n.+1 x-0,0-chain_d C n x)).
  by rewrite subr0 sub0r.
rewrite split linearB in e.
change (-chain_d C n.+1 (source_homotopy_at n.+1 x) +
  (inverse_at n.+1 (chain_map_at f n.+1 x) - source_homotopy_at n (chain_d C n x)) = x) in e.
exact: positive_outer_sum_eq e.
Qed.

Definition target_homotopy : chain_homotopy (chain_composition inverse_chain f) (chain_identity D).
Proof.
refine (@ChainHomotopy R D D _ _ (fun n => (target_homotopy_at n : {linear _ -> _})) _ _).
- exact target_homotopy_zero.
- exact target_homotopy_succ.
Defined.
Definition source_homotopy : chain_homotopy (chain_composition f inverse_chain) (chain_identity C).
Proof.
refine (@ChainHomotopy R C C _ _ (fun n => (source_homotopy_at n : {linear _ -> _})) _ _).
- exact source_homotopy_zero.
- exact source_homotopy_succ.
Defined.
End Inverse.
End DPChainConeHomotopyInverse.
