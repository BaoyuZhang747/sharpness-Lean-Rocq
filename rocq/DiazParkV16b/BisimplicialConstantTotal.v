(** Literal projections from constant-direction total complexes to simplicial chains. *)
From Coq Require Import Arith.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialChains
  SimplicialChainsMaps BisimplicialSet BisimplicialChains
  SimplicialReplacementConstants FirstQuadrantChainBicomplex FirstQuadrantChainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialSet DPSimplicialChains
  DPSimplicialChainMaps DPBisimplicialSet DPBisimplicialChains
  DPSimplicialReplacementConstants DPFirstQuadrantChain DPFirstQuadrantChainTotal.
Local Open Scope ring_scope.

Module DPBisimplicialConstantTotal.
Section Constants.
Variable R : pzRingType.
Variable X : simplicial_set.

Lemma vertical_constant_horizontal p q (a : term R X p.+1) :
  @horizontal_d R (vertical_constant X) p q a = @DPSimplicialChains.boundary R X p a.
Proof. reflexivity. Qed.

Lemma horizontal_constant_vertical p q (a : term R X q.+1) :
  @vertical_d R (horizontal_constant X) p q a = @DPSimplicialChains.boundary R X q a.
Proof. reflexivity. Qed.

Lemma vertical_constant_vertical_zero p (a : term R X p) :
  @vertical_d R (vertical_constant X) p 0%N a = 0.
Proof.
change (\sum_(i < 2) (-1:R)^+i *: free_map R (@idfun (simplex X p)) a = 0).
by rewrite !big_ord_recr big_ord0 !free_map_identity /= scale1r scaleN1r add0r addrN.
Qed.

Lemma horizontal_constant_horizontal_zero q (a : term R X q) :
  @horizontal_d R (horizontal_constant X) 0%N q a = 0.
Proof.
change (\sum_(i < 2) (-1:R)^+i *: free_map R (@idfun (simplex X q)) a = 0).
by rewrite !big_ord_recr big_ord0 !free_map_identity /= scale1r scaleN1r add0r addrN.
Qed.

Definition vertical_projection_at n (a : chain_term (total_chains R (vertical_constant X)) n) :
  term R X n := a n 0%N (Nat.add_0_r n).
Arguments vertical_projection_at n a : clear implicits.

Lemma vertical_projection_linear n : linear (@vertical_projection_at n).
Proof. by move=> r a b. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (@vertical_projection_at n) (@vertical_projection_linear n).

Lemma vertical_projection_commutes n a :
  @DPSimplicialChains.boundary R X n (vertical_projection_at n.+1 a) =
  vertical_projection_at n (chain_d (total_chains R (vertical_constant X)) n a).
Proof.
change (@DPSimplicialChains.boundary R X n (a n.+1 0%N (Nat.add_0_r n.+1)) =
  @horizontal_d R (vertical_constant X) n 0%N
    (a n.+1 0%N (horizontal_input (Nat.add_0_r n))) +
  (-1:R)^+n *: @vertical_d R (vertical_constant X) n 0%N
    (a n 1%N (vertical_input (Nat.add_0_r n)))).
rewrite vertical_constant_vertical_zero scaler0 addr0 vertical_constant_horizontal.
have he : horizontal_input (Nat.add_0_r n) = Nat.add_0_r n.+1 by apply Prop_irrelevance.
by rewrite he.
Qed.

Definition vertical_projection : chain_map (total_chains R (vertical_constant X)) (chains R X) :=
  @ChainMap R (total_chains R (vertical_constant X)) (chains R X)
    (fun n => (@vertical_projection_at n : {linear _ -> _}))
    vertical_projection_commutes.

Definition horizontal_projection_at n (a : chain_term (total_chains R (horizontal_constant X)) n) :
  term R X n := a 0%N n erefl.
Arguments horizontal_projection_at n a : clear implicits.

Lemma horizontal_projection_linear n : linear (@horizontal_projection_at n).
Proof. by move=> r a b. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (@horizontal_projection_at n) (@horizontal_projection_linear n).

Lemma horizontal_projection_commutes n a :
  @DPSimplicialChains.boundary R X n (horizontal_projection_at n.+1 a) =
  horizontal_projection_at n (chain_d (total_chains R (horizontal_constant X)) n a).
Proof.
change (@DPSimplicialChains.boundary R X n (a 0%N n.+1 erefl) =
  @horizontal_d R (horizontal_constant X) 0%N n
    (a 1%N n (@horizontal_input 0%N n n (erefl n))) +
  (-1:R)^+0 *: @vertical_d R (horizontal_constant X) 0%N n
    (a 0%N n.+1 (@vertical_input 0%N n n (erefl n)))).
rewrite horizontal_constant_horizontal_zero add0r expr0 scale1r horizontal_constant_vertical.
have he : @vertical_input 0%N n n (erefl n) = erefl n.+1 by apply Prop_irrelevance.
by rewrite he.
Qed.

Definition horizontal_projection : chain_map (total_chains R (horizontal_constant X)) (chains R X) :=
  @ChainMap R (total_chains R (horizontal_constant X)) (chains R X)
    (fun n => (@horizontal_projection_at n : {linear _ -> _}))
    horizontal_projection_commutes.
End Constants.
End DPBisimplicialConstantTotal.
