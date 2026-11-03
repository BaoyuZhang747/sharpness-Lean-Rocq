(** Literal degree-zero augmentation of the diagonal and total chain complexes. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialChains BisimplicialSet BisimplicialChains
  BisimplicialAlexanderWhitneyChain BisimplicialAlexanderWhitneyZero FirstQuadrantChainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialChains DPBisimplicialSet
  DPBisimplicialChains DPAlexanderWhitneyChain DPAlexanderWhitneyZero DPFirstQuadrantChainTotal.
Local Open Scope ring_scope.

Module DPBisimplicialAugmentation.
Section Augmentation.
Variable R : pzRingType.
Variable X : bisimplicial_set.
Definition total_augmentation : {linear chain_term (total_chains R X) 0%N -> R^o} :=
  (augmentation R (diagonal X) \o @aw_zero_inverse R X : {linear _ -> _}).
Lemma total_augmentation_apply a : total_augmentation a =
  augmentation R (diagonal X) (a 0%N 0%N erefl).
Proof. reflexivity. Qed.
Lemma total_augmentation_aw a :
  total_augmentation (chain_map_at (alexander_whitney R X) 0%N a) = augmentation R (diagonal X) a.
Proof. rewrite /total_augmentation /= aw_zero_left; reflexivity. Qed.

Lemma total_augmentation_boundary (a : chain_term (total_chains R X) 1%N) :
  total_augmentation (chain_d (total_chains R X) 0%N a) = 0.
Proof.
change (augmentation R (diagonal X)
  (@horizontal_d R X 0%N 0%N (a 1%N 0%N (horizontal_input erefl)) +
    (-1:R)^+0 *: @vertical_d R X 0%N 0%N (a 0%N 1%N (vertical_input erefl))) = 0).
rewrite expr0 scale1r linearD horizontal_d_native.
have hh : augmentation R (diagonal X)
  (@DPSimplicialChains.boundary R (horizontal_simplicial X 0%N) 0%N
    (a 1%N 0%N (horizontal_input erefl))) = 0.
  exact (@augmentation_boundary R (horizontal_simplicial X 0%N)
    (a 1%N 0%N (horizontal_input erefl))).
have hv : augmentation R (diagonal X)
  (@vertical_d R X 0%N 0%N (a 0%N 1%N (vertical_input erefl))) = 0.
  exact (@augmentation_boundary R (fobj X 0%N)
    (a 0%N 1%N (vertical_input erefl))).
by rewrite hh hv addr0.
Qed.
End Augmentation.
End DPBisimplicialAugmentation.
