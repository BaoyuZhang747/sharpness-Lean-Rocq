(** The total of the actual zeroth-row bicomplex is the original complex,
    by its literal (n,0) projection and actual single-component inclusion. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainDegreewiseIso ChainQuasiIsomorphism FirstQuadrantChainBicomplex
  FirstQuadrantChainTotal FirstQuadrantChainTotalSupport FirstQuadrantChainRowZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainDegreewiseIso DPChainQuasiIsomorphism DPFirstQuadrantChain
  DPFirstQuadrantChainTotal DPFirstQuadrantChainSupport DPFirstQuadrantChainRowZero.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainRowZeroTotal.
Section Total.
Variable R : pzRingType.
Variable C : chain_complex R.
Let K := row_zero C.

Definition projection_at n (a : total_term K n) : chain_term C n :=
  a n 0%N (Nat.add_0_r n).
Arguments projection_at n a : clear implicits.

Lemma projection_linear n : linear (@projection_at n).
Proof. by move=> r a b. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _
  (@projection_at n) (@projection_linear n).

Lemma projection_commutes n a :
  chain_d C n (projection_at n.+1 a) = projection_at n (chain_d (total_complex K) n a).
Proof.
change (chain_d C n (a n.+1 0%N (Nat.add_0_r n.+1)) =
  chain_d C n (a n.+1 0%N (horizontal_input (Nat.add_0_r n))) + (-1:R)^+n *: 0).
rewrite scaler0 addr0.
have he : horizontal_input (Nat.add_0_r n) = Nat.add_0_r n.+1 by apply Prop_irrelevance.
by rewrite he.
Qed.

Definition total_projection : chain_map (total_complex K) C :=
  @ChainMap R (total_complex K) C (fun n => (@projection_at n : {linear _ -> _}))
    projection_commutes.

Lemma total_projection_injective n : injective (chain_map_at total_projection n).
Proof.
move=> a b hab; apply functional_extensionality_dep=> p;
  apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
case: q h=> [|q] h.
- have hp : p = n by lia.
  subst p.
  have he : h = Nat.add_0_r n by apply Prop_irrelevance.
  rewrite he; exact hab.
- change (a p q.+1 h = b p q.+1 h).
  rewrite (zero_module_unique (a p q.+1 h)) (zero_module_unique (b p q.+1 h)); reflexivity.
Qed.

Definition inclusion_at n (x : chain_term C n) : total_term K n :=
  @total_include R K n 0%N n (Nat.add_0_r n) x.
Arguments inclusion_at n x : clear implicits.

Lemma projection_inclusion n (x : chain_term C n) : projection_at n (inclusion_at n x) = x.
Proof. exact (@total_include_same R K n 0%N n (Nat.add_0_r n) (Nat.add_0_r n) x). Qed.

Lemma inclusion_projection n (a : total_term K n) : inclusion_at n (projection_at n a) = a.
Proof. apply: (@total_projection_injective n); exact: projection_inclusion. Qed.

Lemma total_projection_surjective n (x : chain_term C n) :
  exists a, chain_map_at total_projection n a = x.
Proof. exists (inclusion_at n x); exact: projection_inclusion. Qed.

Definition total_inclusion : chain_map C (total_complex K) :=
  inverse_chain total_projection_injective total_projection_surjective.

Theorem total_inclusion_formula n (x : chain_term C n) :
  chain_map_at total_inclusion n x = inclusion_at n x.
Proof.
apply: (@total_projection_injective n).
transitivity x.
- exact: inverse_chain_right.
- symmetry; exact: projection_inclusion.
Qed.

Theorem total_projection_inclusion n (x : chain_term C n) :
  chain_map_at total_projection n (chain_map_at total_inclusion n x) = x.
Proof. exact: inverse_chain_right. Qed.

Theorem total_inclusion_projection n (a : total_term K n) :
  chain_map_at total_inclusion n (chain_map_at total_projection n a) = a.
Proof. exact: inverse_chain_left. Qed.

Definition total_homology_iso n : @isomorphism (module_category R)
  [the lmodType R of homology (total_complex K) n] [the lmodType R of homology C n] :=
  degreewise_homology_iso total_projection_injective total_projection_surjective n.

Theorem total_projection_quasi_isomorphism : quasi_isomorphism total_projection.
Proof.
move=> n; split.
- move=> x y h.
  rewrite -(inverse_homology_left total_projection_injective total_projection_surjective x)
    -(inverse_homology_left total_projection_injective total_projection_surjective y) h.
  reflexivity.
- move=> y; exists (homology_map total_inclusion n y); exact: inverse_homology_right.
Qed.
End Total.
End DPFirstQuadrantChainRowZeroTotal.
