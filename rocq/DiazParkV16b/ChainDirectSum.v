(** Actual arbitrary dependent direct sums of nonnegative chain complexes. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModuleDirectSums CategoryModuleDirectSumMaps.
From DiazParkV16b Require Import ChainComplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex.
Local Open Scope ring_scope.

Module DPChainDirectSum.
Section Sum.
Variable R : pzRingType.
Variable I : Type.
Variable C : I -> chain_complex R.

Definition direct_sum_term n := module_sum_type (fun i => chain_term (C i) n).
Definition direct_sum_d n : {linear direct_sum_term n.+1 -> direct_sum_term n} :=
  (sum_map (fun i => chain_d (C i) n) : {linear _ -> _}).
Lemma direct_sum_d_squared n x : direct_sum_d n (direct_sum_d n.+1 x) = 0.
Proof.
apply: sum_coefficient_ext => i.
change (chain_d (C i) n (chain_d (C i) n.+1 (sum_coefficient x i)) = 0).
exact: chain_d2.
Qed.
Definition direct_sum : chain_complex R :=
  @ChainComplex R direct_sum_term direct_sum_d direct_sum_d_squared.

Lemma direct_sum_d_coefficient n x i :
  sum_coefficient (chain_d direct_sum n x) i = chain_d (C i) n (sum_coefficient x i).
Proof. reflexivity. Qed.
Lemma direct_sum_d_single n i (x : chain_term (C i) n.+1) :
  chain_d direct_sum n (@sum_single R I (fun j => chain_term (C j) n.+1) i x) =
    @sum_single R I (fun j => chain_term (C j) n) i (chain_d (C i) n x).
Proof. exact: sum_map_single. Qed.

Definition direct_sum_inclusion i : chain_map (C i) direct_sum.
Proof.
refine (@ChainMap R (C i) direct_sum (fun n =>
  (@sum_single R I (fun j => chain_term (C j) n) i : {linear _ -> _})) _).
move=> n x; exact: direct_sum_d_single.
Defined.
Definition direct_sum_projection i : chain_map direct_sum (C i).
Proof.
refine (@ChainMap R direct_sum (C i) (fun n =>
  (@sum_evaluation R I (fun j => chain_term (C j) n) i : {linear _ -> _})) _).
by move=> n x.
Defined.

Lemma direct_sum_cycle n (x : chain_term direct_sum n) :
  @cycle R direct_sum n x <-> forall i, @cycle R (C i) n (sum_coefficient x i).
Proof.
case: n x => [|n] x; first by split.
split=> h.
- move=> i; exact: (congr1 (fun z => sum_coefficient z i) h).
- apply: sum_coefficient_ext => i; exact: h.
Qed.

Lemma direct_sum_boundary n (x : chain_term direct_sum n) :
  @boundary R direct_sum n x <-> forall i, @boundary R (C i) n (sum_coefficient x i).
Proof.
split.
- move=> [y hy] i; exists (sum_coefficient y i).
  exact: (congr1 (fun z => sum_coefficient z i) hy).
- move=> h.
  pose y := @sum_preimage R I (fun i => chain_term (C i) n.+1)
    (fun i => chain_term (C i) n) (fun i => chain_d (C i) n) x h.
  exists y; exact: sum_preimage_spec.
Qed.
End Sum.

Section Maps.
Variable R : pzRingType.
Variable I : Type.
Variables C D : I -> chain_complex R.
Variable f : forall i, chain_map (C i) (D i).
Definition direct_sum_map : chain_map (direct_sum C) (direct_sum D).
Proof.
refine (@ChainMap R (direct_sum C) (direct_sum D)
  (fun n => (sum_map (fun i => chain_map_at (f i) n) : {linear _ -> _})) _).
move=> n x; apply: sum_coefficient_ext => i.
change (chain_d (D i) n (chain_map_at (f i) n.+1 (sum_coefficient x i)) =
  chain_map_at (f i) n (chain_d (C i) n (sum_coefficient x i))).
exact: chain_map_commutes.
Defined.
Lemma direct_sum_map_coefficient n x i :
  sum_coefficient (chain_map_at direct_sum_map n x) i = chain_map_at (f i) n (sum_coefficient x i).
Proof. reflexivity. Qed.
Lemma direct_sum_map_single n i (x : chain_term (C i) n) :
  chain_map_at direct_sum_map n (@sum_single R I (fun j => chain_term (C j) n) i x) =
    @sum_single R I (fun j => chain_term (D j) n) i (chain_map_at (f i) n x).
Proof. exact: sum_map_single. Qed.
End Maps.
End DPChainDirectSum.
