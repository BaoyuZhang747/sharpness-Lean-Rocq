(** The actual bicomplex concentrated in its zeroth row. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModuleProducts.
From DiazParkV16b Require Import ChainComplex FirstQuadrantChainBicomplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPFirstQuadrantChain.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainRowZero.
Section RowZero.
Variable R : pzRingType.

Definition zero_module : lmodType R :=
  module_product_type (fun _ : False => [the lmodType R of R^o]).

Lemma zero_module_unique (x : zero_module) : x = 0.
Proof. apply functional_extensionality_dep=> h; exact: False_ind h. Qed.

Definition zero_map (U V : lmodType R) (_ : U) : V := 0.
Lemma zero_map_linear (U V : lmodType R) : linear (@zero_map U V).
Proof. by move=> r x y; rewrite /zero_map scaler0 addr0. Qed.
HB.instance Definition _ (U V : lmodType R) := GRing.isLinear.Build R _ _ _
  (@zero_map U V) (@zero_map_linear U V).

Variable C : chain_complex R.

Definition row_term p q : lmodType R :=
  match q with 0%N => chain_term C p | _ => zero_module end.

Definition row_horizontal p q : {linear row_term p.+1 q -> row_term p q} :=
  match q as k return {linear row_term p.+1 k -> row_term p k} with
  | 0%N => chain_d C p
  | _ => (@zero_map zero_module zero_module : {linear _ -> _})
  end.

Definition row_vertical p q : {linear row_term p q.+1 -> row_term p q} :=
  (@zero_map (row_term p q.+1) (row_term p q) : {linear _ -> _}).

Lemma row_horizontal_squared p q x : row_horizontal p q (row_horizontal p.+1 q x) = 0.
Proof. case: q x=> [|q] x; [exact: chain_d2 | reflexivity]. Qed.

Lemma row_vertical_squared p q x : row_vertical p q (row_vertical p q.+1 x) = 0.
Proof. reflexivity. Qed.

Lemma row_horizontal_vertical p q x :
  row_horizontal p q (row_vertical p.+1 q x) = row_vertical p q (row_horizontal p q.+1 x).
Proof. change (row_horizontal p q 0 = 0); exact: linear0. Qed.

Definition row_zero : bicomplex R :=
  @Bicomplex R row_term row_horizontal row_vertical
    row_horizontal_squared row_vertical_squared row_horizontal_vertical.

Lemma row_zero_zero p : bicomplex_term row_zero p 0%N = chain_term C p.
Proof. reflexivity. Qed.

Lemma row_zero_positive p q (x : bicomplex_term row_zero p q.+1) : x = 0.
Proof. exact: zero_module_unique. Qed.
End RowZero.
End DPFirstQuadrantChainRowZero.
