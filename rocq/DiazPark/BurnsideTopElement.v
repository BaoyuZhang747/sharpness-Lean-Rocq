From mathcomp Require Import all_boot all_algebra generic_quotient boolp.
From DiazPark Require Import Category CategoryFinite CategoryFiniteClasses
  CategoryFiniteProducts CategoryFiniteSlice BurnsideAlgebra.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section TopProduct.
Variable C : finite_category.
Variables S P : fc_object C.
Variable D : @finite_product_decomposition (fc_category C) S P.

Definition burnside_top_object (i : fp_index D) : fc_object (@fc_slice C P) :=
  existT _ (fp_apex D i) (fp_right D i).

Variable X : fc_object (@fc_slice C P).

Definition burnside_top_factor :=
  {i : fp_index D & fc_hom (@fc_slice C P) X (burnside_top_object i)}.

Definition burnside_top_forget (t : burnside_top_factor) :
    fp_factors D (projT1 X) :=
  existT _ (projT1 t) (val (projT2 t)).

Lemma burnside_top_forget_injective : injective burnside_top_forget.
Proof.
move=> [i f] [j g] h.
have he := existT_inj1 h; cbn in he; destruct he.
have hm := existT_inj2 h; f_equal; exact: val_inj hm.
Qed.

Definition burnside_top_encode (t : burnside_top_factor) : fc_hom C (projT1 X) S :=
  fc_compose (val (projT2 t)) (fp_left D (projT1 t)).

Definition burnside_top_decode (f : fc_hom C (projT1 X) S) : burnside_top_factor.
Proof.
refine (existT _ (projT1 (fp_lift D f (projT2 X))) _).
exists (projT2 (fp_lift D f (projT2 X))); apply/eqP.
exact (fp_lift_right D f (projT2 X)).
Defined.

Lemma burnside_top_encode_decode : cancel burnside_top_decode burnside_top_encode.
Proof. move=> f; exact (fp_lift_left D f (projT2 X)). Qed.

Lemma burnside_top_forget_decode f :
    burnside_top_forget (burnside_top_decode f) = fp_lift D f (projT2 X).
Proof.
change (existT _ (projT1 (fp_lift D f (projT2 X)))
  (projT2 (fp_lift D f (projT2 X))) = fp_lift D f (projT2 X)).
by case: (fp_lift D f (projT2 X)).
Qed.

Lemma burnside_top_decode_encode : cancel burnside_top_encode burnside_top_decode.
Proof.
move=> [i f]; apply: burnside_top_forget_injective.
rewrite burnside_top_forget_decode /burnside_top_encode /=.
transitivity (fp_lift D (fc_compose (val f) (fp_left D i))
  (fc_compose (val f) (fp_right D i))).
- apply: congr1; symmetry; exact: eqP (valP f).
- exact: fp_unique.
Qed.

Theorem burnside_top_factor_cardinality :
    (\sum_(i : fp_index D) #|fc_hom (@fc_slice C P) X (burnside_top_object i)| =
      #|fc_hom C (projT1 X) S|)%N.
Proof.
have h : bijective burnside_top_encode.
  exists burnside_top_decode; [exact: burnside_top_decode_encode | exact: burnside_top_encode_decode].
have hc := @bij_eq_card [the finType of burnside_top_factor]
  (fc_hom C (projT1 X) S) burnside_top_encode h.
by rewrite card_tagged sumnE big_map big_enum in hc.
Qed.

End TopProduct.

Arguments burnside_top_object {_ _ _} _ _.

Section TopMarks.
Variable C : finite_category.
Variables S P : fc_object C.
Variable D : @finite_product_decomposition (fc_category C) S P.
Variable R : comPzRingType.

Definition burnside_top_element : burnside_module (@fc_slice C P) R :=
  \sum_(i : fp_index D) burnside_basis R (fc_class (burnside_top_object D i)).

Theorem burnside_top_mark (X : fc_object (@fc_slice C P)) :
    burnside_mark X burnside_top_element = (#|fc_hom C (projT1 X) S|)%:R.
Proof.
rewrite /burnside_top_element /burnside_mark.
under eq_bigr do rewrite sum_ffunE mulr_suml.
rewrite exchange_big.
change (\sum_i burnside_mark X (burnside_basis R (fc_class (burnside_top_object D i))) =
  (#|fc_hom C (projT1 X) S|)%:R).
under eq_bigr do rewrite burnside_mark_basis fc_mark_class.
rewrite -natr_sum; congr (_%:R); exact: burnside_top_factor_cardinality.
Qed.

End TopMarks.

Print Assumptions burnside_top_factor_cardinality.
Print Assumptions burnside_top_mark.
