(** Homological cofinality from explicit exactness of the actual augmented
    comma-string chains. No global cofinality or Kan exactness law is assumed. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryComma CategoryModules CategoryDerivedLimits.
From DiazParkV16b Require Import CategoryStringChains CategoryInducedBarTerms
  CategoryInducedBarDifferential CategoryInducedBarAugmentation
  CategoryInducedBarCommaChains CategoryInducedBarResolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Definition category_string_augmented_exact (R : pzRingType) (C : category) : Prop :=
  (forall a : R^o, exists v, category_string_augmentation R C v = a) /\
  (forall v, category_string_augmentation R C v = 0 ->
    exists w, @category_string_boundary R C 0%N w = v) /\
  (forall n (v : category_string_term R C n.+1),
    @category_string_boundary R C n v = 0 ->
    exists w, @category_string_boundary R C n.+1 w = v).

Section Cofinality.
Variable R : comPzRingType.
Variables C D : category.
Variable q : functor C D.
Hypothesis commas_exact : forall d, category_string_augmented_exact R (structured_category q d).

Lemma induced_bar_augmentation_surjective_of_comma d (a : R^o) :
    exists v, module_hom_fun (component (induced_bar_augmentation R q) d) v = a.
Proof.
destruct (proj1 (commas_exact d) a) as [v hv].
exists (@induced_bar_comma_forward R C D q d 0%N v).
by rewrite induced_bar_comma_augmentation.
Qed.

Lemma induced_bar_augmentation_exact_of_comma d (v : fobj (induced_bar_term R q 0%N) d) :
    module_hom_fun (component (induced_bar_augmentation R q) d) v = 0 ->
    exists w, module_hom_fun (component (induced_bar_boundary R q 0%N) d) w = v.
Proof.
intro hv.
pose a := @induced_bar_comma_backward R C D q d 0%N v.
have ha : category_string_augmentation R (structured_category q d) a = 0.
  rewrite -induced_bar_comma_augmentation /a induced_bar_comma_forward_backward.
  exact hv.
destruct (proj1 (proj2 (commas_exact d)) a ha) as [w hw].
exists (@induced_bar_comma_forward R C D q d 1%N w).
rewrite induced_bar_comma_forward_boundary hw /a induced_bar_comma_forward_backward.
reflexivity.
Qed.

Lemma induced_bar_successor_exact_of_comma n d (v : fobj (induced_bar_term R q n.+1) d) :
    module_hom_fun (component (induced_bar_boundary R q n) d) v = 0 ->
    exists w, module_hom_fun (component (induced_bar_boundary R q n.+1) d) w = v.
Proof.
intro hv.
pose a := @induced_bar_comma_backward R C D q d n.+1 v.
have ha : @category_string_boundary R (structured_category q d) n a = 0.
  rewrite /a induced_bar_comma_backward_boundary hv linear0; reflexivity.
destruct (proj2 (proj2 (commas_exact d)) n a ha) as [w hw].
exists (@induced_bar_comma_forward R C D q d n.+2 w).
rewrite induced_bar_comma_forward_boundary hw /a induced_bar_comma_forward_backward.
reflexivity.
Qed.

Definition induced_bar_higher_limit_iso_of_comma_exact
    (M : module_codiagram R D) n : @isomorphism (module_category R)
    (derived_limit R M n) (derived_limit R (functor_comp (functor_op q) M) n) :=
  @induced_bar_higher_limit_iso R C D q
    induced_bar_augmentation_surjective_of_comma
    induced_bar_augmentation_exact_of_comma induced_bar_successor_exact_of_comma M n.
End Cofinality.

Arguments induced_bar_higher_limit_iso_of_comma_exact R {C D} q commas_exact M n.
