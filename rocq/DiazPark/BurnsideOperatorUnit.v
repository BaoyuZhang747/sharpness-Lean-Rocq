From mathcomp Require Import all_boot all_algebra generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteClasses
  CategoryFiniteProducts CategoryFinitePullbacks CategoryFiniteSlice
  CategoryFiniteSliceProducts BurnsideAlgebra BurnsideMarkAlgebra
  BurnsideTopElement BurnsideOperators MackeyPair.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section OperatorUnit.
Variable C : finite_category.
Variable R : comPzRingType.
Variable M : mackey_pair R (fc_category C).
Variable P : fc_object C.

Lemma burnside_action_one (x : pair_value M P) :
    burnside_action (M := M)
      (burnside_basis R (fc_class (@fc_slice_terminal_point C P))) x = x.
Proof.
rewrite burnside_action_basis burnside_class_operatorE.
change (pair_push M (@identity (fc_category C) P)
  (pair_pull M (@identity (fc_category C) P) x) = x).
by rewrite pair_pull_id pair_push_id.
Qed.

Variable S : fc_object C.
Variable D : @finite_product_decomposition (fc_category C) S P.

Theorem burnside_action_top (x : pair_value M P) :
    burnside_action (M := M) (burnside_top_element D R) x =
      \sum_(i : fp_index D) pair_push M (fp_right D i) (pair_pull M (fp_right D i) x).
Proof.
change (burnside_action_at (M := M) x (burnside_top_element D R) =
  \sum_(i : fp_index D) pair_push M (fp_right D i) (pair_pull M (fp_right D i) x)).
rewrite /burnside_top_element /burnside_action_at /burnside_action.
under eq_bigr do rewrite sum_ffunE scaler_suml.
rewrite exchange_big.
apply: eq_bigr=> i _.
change (burnside_action (M := M) (burnside_basis R
  (fc_class (burnside_top_object D i))) x =
  pair_push M (fp_right D i) (pair_pull M (fp_right D i) x)).
rewrite burnside_action_basis burnside_class_operatorE.
reflexivity.
Qed.

End OperatorUnit.

Print Assumptions burnside_action_one.
Print Assumptions burnside_action_top.
