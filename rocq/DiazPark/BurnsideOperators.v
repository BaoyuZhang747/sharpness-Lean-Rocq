From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFiniteClasses
  CategoryFiniteProducts CategoryFinitePullbacks CategoryFiniteSlice
  CategoryFiniteSliceProducts BurnsideAlgebra MackeyPair.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Section Operators.
Variable C : finite_category.
Variable R : comPzRingType.
Variable M : mackey_pair R (fc_category C).
Variable P : fc_object C.
Local Notation Slice := (@fc_slice C P).

Definition burnside_slice_operator (A : fc_object Slice) (x : pair_value M P) :=
  pair_push M (projT2 A) (pair_pull M (projT2 A) x).

Definition burnside_slice_underlying_iso (A B : fc_object Slice)
    (e : @isomorphism (fc_category Slice) A B) :
    @isomorphism (fc_category C) (projT1 A) (projT1 B).
Proof.
refine (@Build_isomorphism (fc_category C) (projT1 A) (projT1 B)
  (val (iso_hom e)) (val (iso_inv e)) _ _).
- exact (congr1 val (iso_hom_inv e)).
- exact (congr1 val (iso_inv_hom e)).
Defined.

Lemma burnside_slice_operator_iso A B
    (e : @isomorphism (fc_category Slice) A B) x :
    burnside_slice_operator A x = burnside_slice_operator B x.
Proof.
pose u := burnside_slice_underlying_iso e.
have hf : fc_compose (iso_hom u) (projT2 B) = projT2 A := eqP (valP (iso_hom e)).
rewrite /burnside_slice_operator -hf pair_pull_comp pair_push_comp.
rewrite (pair_pull_iso u) -(pair_push_comp (iso_inv u) (iso_hom u))
  iso_inv_hom pair_push_id.
reflexivity.
Qed.

Definition burnside_class_operator (a : fc_iso_class Slice) :=
  burnside_slice_operator (repr a).

Lemma burnside_class_operatorE (A : fc_object Slice) x :
    burnside_class_operator (fc_class A) x = burnside_slice_operator A x.
Proof. exact (burnside_slice_operator_iso (fc_repr_iso A) x). Qed.

Lemma burnside_slice_operator_linear A : linear (burnside_slice_operator A).
Proof. move=> a x y; by rewrite /burnside_slice_operator !linearP. Qed.

HB.instance Definition _ A := GRing.isLinear.Build R
  (pair_value M P) (pair_value M P) _
  (burnside_slice_operator A) (burnside_slice_operator_linear A).

Definition burnside_action (v : burnside_module Slice R) (x : pair_value M P) :=
  \sum_a v a *: burnside_class_operator a x.

Lemma burnside_action_basis a x :
    burnside_action (burnside_basis R a) x = burnside_class_operator a x.
Proof.
rewrite /burnside_action (bigD1 a) //= /burnside_basis ffunE eqxx scale1r.
rewrite big1 ?addr0 // => b /negbTE hb.
by rewrite ffunE eq_sym hb scale0r.
Qed.

Definition burnside_action_at (x : pair_value M P) (v : burnside_module Slice R) :=
  burnside_action v x.

Lemma burnside_action_linear_coefficient x : linear (burnside_action_at x).
Proof.
move=> a v w; rewrite /burnside_action scaler_sumr -big_split /=.
apply: eq_bigr=> b _.
by rewrite !ffunE burnside_regular_scale scalerDl scalerA.
Qed.

HB.instance Definition _ x := GRing.isLinear.Build R
  [the lmodType R of burnside_module Slice R] (pair_value M P) _
  (burnside_action_at x) (burnside_action_linear_coefficient x).

Lemma burnside_action_linear_value v : linear (burnside_action v).
Proof.
move=> a x y; rewrite /burnside_action scaler_sumr -big_split /=.
apply: eq_bigr=> b _.
rewrite /burnside_class_operator linearP scalerDr !scalerA.
by rewrite mulrC.
Qed.

HB.instance Definition _ v := GRing.isLinear.Build R
  (pair_value M P) (pair_value M P) _
  (burnside_action v) (burnside_action_linear_value v).

Variable pullbacks : forall (A B : fc_object C)
  (f : fc_hom C A P) (g : fc_hom C B P),
  @finite_pullback_decomposition (fc_category C) A B P f g.

Hypothesis pullback_mackey : forall (A B : fc_object C)
  (f : fc_hom C A P) (g : fc_hom C B P) (x : pair_value M A),
  pair_pull M g (pair_push M f x) =
    \sum_(i : pb_index (pullbacks f g))
      pair_push M (pb_right (pullbacks f g) i)
        (pair_pull M (pb_left (pullbacks f g) i) x).

Definition burnside_slice_products (A B : fc_object Slice) :
    @finite_product_decomposition (fc_category Slice) A B :=
  fc_pullback_slice_product (pullbacks (projT2 A) (projT2 B)).

Lemma burnside_operator_product A B x :
    burnside_slice_operator B (burnside_slice_operator A x) =
    \sum_(i : fp_index (burnside_slice_products A B))
      burnside_slice_operator (fp_apex (burnside_slice_products A B) i) x.
Proof.
rewrite /burnside_slice_operator (pullback_mackey (projT2 A) (projT2 B)) linear_sum.
apply: eq_bigr=> i _.
rewrite -pair_push_comp -pair_pull_comp.
have h := pb_commutes (pullbacks (projT2 A) (projT2 B)) i.
rewrite -h; reflexivity.
Qed.

Lemma burnside_action_basis_product a b x :
    burnside_action (burnside_basis_product R burnside_slice_products a b) x =
      burnside_class_operator b (burnside_class_operator a x).
Proof.
change (burnside_action_at x
  (burnside_basis_product R burnside_slice_products a b) =
  burnside_class_operator b (burnside_class_operator a x)).
rewrite /burnside_basis_product linear_sum /=.
under eq_bigr do rewrite /burnside_action_at burnside_action_basis burnside_class_operatorE.
symmetry; exact: burnside_operator_product.
Qed.

Theorem burnside_action_mul v w x :
    burnside_action (burnside_mul burnside_slice_products v w) x =
      burnside_action w (burnside_action v x).
Proof.
change (burnside_action_at x (burnside_mul burnside_slice_products v w) =
  burnside_action w (burnside_action v x)).
rewrite /burnside_mul linear_sum /=.
under eq_bigr do rewrite linear_sum /=.
under eq_bigr do under eq_bigr do rewrite linearZ /= /burnside_action_at burnside_action_basis_product.
rewrite [RHS]/burnside_action.
under [RHS]eq_bigr do rewrite /burnside_class_operator linear_sum scaler_sumr.
under [RHS]eq_bigr do under eq_bigr do rewrite linearZ scalerA.
rewrite [RHS]exchange_big.
apply: eq_bigr=> a _; apply: eq_bigr=> b _.
by rewrite mulrC.
Qed.

End Operators.

Print Assumptions burnside_class_operatorE.
Print Assumptions burnside_action_mul.
