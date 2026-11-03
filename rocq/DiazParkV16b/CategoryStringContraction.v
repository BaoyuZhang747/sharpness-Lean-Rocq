(** Exact augmented strings from an actual two-sided categorical contraction.
    The natural transformations are converted to their literal prism maps. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarPaths BarFreeModule.
From DiazParkV16b Require Import ChainComplex CategoryStringChains
  CategoryStringChainsMaps CategoryStringChainHomotopy CategoryStringConstantChains
  CategoryInducedBarCofinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule DPChainComplex
  DPCategoryStringChainHomotopy DPCategoryStringConstant.
Local Open Scope ring_scope.

Module DPCategoryStringContraction.
Section Contraction.
Variable R : pzRingType.
Variable C : category.
Variable b : C.
Variable J : functor C C.
Variable alpha : nat_trans (functor_id C) J.
Variable beta : nat_trans (constant_functor C b) J.

Lemma contraction_augmentation_surjective (a : R^o) :
  exists v, category_string_augmentation R C v = a.
Proof.
exists ((a : R) *: (free_basis R (existT _ b tt) : category_string_term R C 0%N)).
rewrite linearZ category_string_augmentation_basis.
exact: mulr1.
Qed.

Lemma contraction_zero_exact (v : category_string_term R C 0%N) :
  category_string_augmentation R C v = 0 ->
  exists w, @category_string_boundary R C 0%N w = v.
Proof.
move=> hv.
exists (- @prism_chain_at R C C (functor_id C) J alpha 0%N v +
  @prism_chain_at R C C (constant_functor C b) J beta 0%N v).
rewrite linearD linearN.
change (- @category_string_boundary R C 0%N
  (@prism_chain_at R C C (functor_id C) J alpha 0%N v) +
  @category_string_boundary R C 0%N
  (@prism_chain_at R C C (constant_functor C b) J beta 0%N v) = v).
rewrite !prism_chain_zero category_string_map_identity.
rewrite constant_zero_augmentation hv scale0r subr0.
by rewrite opprB subrK.
Qed.

Lemma contraction_successor_exact n (v : category_string_term R C n.+1) :
  @category_string_boundary R C n v = 0 ->
  exists w, @category_string_boundary R C n.+1 w = v.
Proof.
move=> hv.
have ha := @prism_chain_succ R C C (functor_id C) J alpha n v.
have hb := @prism_chain_succ R C C (constant_functor C b) J beta n v.
rewrite hv linear0 addr0 category_string_map_identity in ha.
rewrite hv linear0 addr0 in hb.
case: (@constant_positive_boundary C C b R n v hv)=> w hw.
exists (- @prism_chain_at R C C (functor_id C) J alpha n.+1 v +
  @prism_chain_at R C C (constant_functor C b) J beta n.+1 v + w).
rewrite !linearD linearN.
change (- @category_string_boundary R C n.+1
  (@prism_chain_at R C C (functor_id C) J alpha n.+1 v) +
  @category_string_boundary R C n.+1
  (@prism_chain_at R C C (constant_functor C b) J beta n.+1 v) +
  @category_string_boundary R C n.+1 w = v).
rewrite ha hb hw.
by rewrite opprB addrA subrK subrK.
Qed.

Theorem category_string_augmented_exact_of_contraction :
  category_string_augmented_exact R C.
Proof.
split; first exact contraction_augmentation_surjective.
split; [exact contraction_zero_exact | exact contraction_successor_exact].
Qed.
End Contraction.
End DPCategoryStringContraction.

Print Assumptions DPCategoryStringContraction.category_string_augmented_exact_of_contraction.
