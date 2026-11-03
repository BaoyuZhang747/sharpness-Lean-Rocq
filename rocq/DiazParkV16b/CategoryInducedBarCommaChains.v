(** Actual inverse chain maps between the evaluated induced bar and the
    native comma-string chains, preserving the literal augmentation. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryComma CategoryModules CategoryModuleLinear
  BarPaths BarFreeModule.
From DiazParkV16b Require Import ChainComplex CategoryStringChains CategoryInducedBarTerms
  CategoryInducedBarDifferential CategoryInducedBarAugmentation
  CategoryInducedBarCommaPaths CategoryInducedBarCommaFaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule DPChainComplex.
Local Open Scope ring_scope.

Section ChainMaps.
Variable R : pzRingType.
Variables C D : category.
Variable q : functor C D.
Variable d : D.

Definition induced_bar_comma_forward n :
    {linear category_string_term R (structured_category q d) n ->
      induced_bar_term_obj R q n d} :=
  free_map R (@induced_bar_comma_to_basis C D q d n).

Definition induced_bar_comma_backward n :
    {linear induced_bar_term_obj R q n d ->
      category_string_term R (structured_category q d) n} :=
  free_map R (@induced_bar_basis_to_comma C D q d n).

Lemma induced_bar_comma_forward_backward n (v : induced_bar_term_obj R q n d) :
    induced_bar_comma_forward n (induced_bar_comma_backward n v) = v.
Proof.
apply (free_lift_ext
  (g := (induced_bar_comma_forward n \o induced_bar_comma_backward n : {linear _ -> _}))
  (h := (idfun : {linear _ -> _}))).
intro s; rewrite /= /induced_bar_comma_forward /induced_bar_comma_backward !free_map_basis.
by rewrite induced_bar_comma_basis_inverse.
Qed.

Lemma induced_bar_comma_backward_forward n
    (v : category_string_term R (structured_category q d) n) :
    induced_bar_comma_backward n (induced_bar_comma_forward n v) = v.
Proof.
apply (free_lift_ext
  (g := (induced_bar_comma_backward n \o induced_bar_comma_forward n : {linear _ -> _}))
  (h := (idfun : {linear _ -> _}))).
intro s; rewrite /= /induced_bar_comma_forward /induced_bar_comma_backward !free_map_basis.
by rewrite induced_bar_basis_comma_inverse.
Qed.

Lemma induced_bar_comma_forward_injective n : injective (induced_bar_comma_forward n).
Proof.
intros v w h.
rewrite -(induced_bar_comma_backward_forward v) -(induced_bar_comma_backward_forward w).
by rewrite h.
Qed.

Lemma induced_bar_comma_forward_boundary n
    (v : category_string_term R (structured_category q d) n.+1) :
    module_hom_fun (component (induced_bar_boundary R q n) d)
      (induced_bar_comma_forward n.+1 v) =
    induced_bar_comma_forward n (@category_string_boundary R (structured_category q d) n v).
Proof.
apply (free_lift_ext
  (g := (module_hom_to_linear (component (induced_bar_boundary R q n) d) \o
    induced_bar_comma_forward n.+1 : {linear _ -> _}))
  (h := (induced_bar_comma_forward n \o
    @category_string_boundary R (structured_category q d) n : {linear _ -> _}))).
intro s.
change (module_hom_fun (component (induced_bar_boundary R q n) d)
  (free_map R (@induced_bar_comma_to_basis C D q d n.+1) (free_basis R s)) =
  induced_bar_comma_forward n (@category_string_boundary R (structured_category q d) n (free_basis R s))).
rewrite free_map_basis induced_bar_comma_boundary_generator /category_string_boundary linear_sum.
apply eq_bigr; intros i _; rewrite linearZ.
by rewrite /category_string_face /induced_bar_comma_forward !free_map_basis.
Qed.

Definition induced_bar_comma_forward_chain :
    chain_map (category_string_chain R (structured_category q d))
      (induced_bar_evaluation_chain R q d) :=
  @ChainMap R (category_string_chain R (structured_category q d))
    (induced_bar_evaluation_chain R q d) induced_bar_comma_forward induced_bar_comma_forward_boundary.

Lemma induced_bar_comma_backward_boundary n (v : induced_bar_term_obj R q n.+1 d) :
    @category_string_boundary R (structured_category q d) n
      (induced_bar_comma_backward n.+1 v) =
    induced_bar_comma_backward n
      (module_hom_fun (component (induced_bar_boundary R q n) d) v).
Proof.
apply induced_bar_comma_forward_injective.
rewrite -induced_bar_comma_forward_boundary !induced_bar_comma_forward_backward.
reflexivity.
Qed.

Definition induced_bar_comma_backward_chain :
    chain_map (induced_bar_evaluation_chain R q d)
      (category_string_chain R (structured_category q d)) :=
  @ChainMap R (induced_bar_evaluation_chain R q d)
    (category_string_chain R (structured_category q d)) induced_bar_comma_backward
      induced_bar_comma_backward_boundary.
End ChainMaps.

Section Augmentation.
Variable R : comPzRingType.
Variables C D : category.
Variable q : functor C D.
Variable d : D.

Theorem induced_bar_comma_augmentation
    (v : category_string_term R (structured_category q d) 0%N) :
    module_hom_fun (component (induced_bar_augmentation R q) d)
      (@induced_bar_comma_forward R C D q d 0%N v) =
    category_string_augmentation R (structured_category q d) v.
Proof.
apply (free_lift_ext
  (g := (module_hom_to_linear (component (induced_bar_augmentation R q) d) \o
    @induced_bar_comma_forward R C D q d 0%N : {linear _ -> _}))
  (h := category_string_augmentation R (structured_category q d))).
intro s.
change (module_hom_fun (component (induced_bar_augmentation R q) d)
  (free_map R (@induced_bar_comma_to_basis C D q d 0%N) (free_basis R s)) =
  category_string_augmentation R (structured_category q d) (free_basis R s)).
by rewrite free_map_basis
  induced_bar_augmentation_basis category_string_augmentation_basis.
Qed.
End Augmentation.
