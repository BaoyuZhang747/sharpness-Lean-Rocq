(** Representable product decompositions give the actual discrete initial
    family in the comma category computing right Kan extension from a slice.
    No centricity or saturation premise is hidden in this generic bridge. *)
From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category CategoryComma CategoryStructured
  CategoryInitialFamily CategoryFiniteProducts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SliceProductFamily.
Variable C : category.
Variables P Q : C.
Variable E : finite_product_decomposition P Q.

Definition product_slice_object (i : fp_index E) : over_category C P :=
  @Build_costructured_object C C (functor_id C) P (fp_apex E i) (fp_left E i).

Definition product_comma_object (i : fp_index E) :
    structured_category (functor_op (@over_forget C P)) Q :=
  structured_point (functor_op (@over_forget C P))
    (product_slice_object i) (fp_right E i).

Definition product_comma_factor_forget
    (X : structured_category (functor_op (@over_forget C P)) Q)
    (z : {i : fp_index E & hom
      (structured_category (functor_op (@over_forget C P)) Q)
      (product_comma_object i) X}) :
    fp_factors E (costructured_source (structured_source X)) :=
  existT _ (projT1 z) (costructured_map (structured_map (projT2 z))).

Lemma product_comma_factor_forget_injective
    (X : structured_category (functor_op (@over_forget C P)) Q) :
    injective (@product_comma_factor_forget X).
Proof.
  intros [i h] [j k] e.
  pose proof (existT_inj1 e) as eij. simpl in eij. destruct eij.
  pose proof (existT_inj2 e) as ehk.
  f_equal. apply costructured_hom_ext. apply costructured_hom_ext. exact ehk.
Qed.

Lemma product_comma_factor_encode
    (X : structured_category (functor_op (@over_forget C P)) Q)
    (z : {i : fp_index E & hom
      (structured_category (functor_op (@over_forget C P)) Q)
      (product_comma_object i) X}) :
    fp_encode E (product_comma_factor_forget z) =
      (costructured_arrow (structured_source X), structured_arrow X).
Proof.
  destruct z as [i f]. unfold product_comma_factor_forget, fp_encode. simpl.
  apply f_equal2.
  - exact (costructured_commutes (structured_map f)).
  - exact (structured_commutes f).
Qed.

Definition product_comma_choice
    (X : structured_category (functor_op (@over_forget C P)) Q) :
    {i : fp_index E & hom
      (structured_category (functor_op (@over_forget C P)) Q)
      (product_comma_object i) X}.
Proof.
  pose (z := fp_lift E (costructured_arrow (structured_source X))
    (structured_arrow X)).
  exists (projT1 z).
  unshelve refine (@structured_morphism (opposite (over_category C P)) (opposite C)
    (functor_op (@over_forget C P)) Q (product_comma_object (projT1 z)) X
    (@Build_costructured_hom C C (functor_id C) P (structured_source X)
      (product_slice_object (projT1 z)) (projT2 z) _) _).
  - exact (fp_lift_left E (costructured_arrow (structured_source X))
      (structured_arrow X)).
  - exact (fp_lift_right E (costructured_arrow (structured_source X))
      (structured_arrow X)).
Defined.

Definition product_comma_initial_family :
    initial_family (structured_category (functor_op (@over_forget C P)) Q).
Proof.
  refine (@Build_initial_family
    (structured_category (functor_op (@over_forget C P)) Q)
    (fp_index E) product_comma_object product_comma_choice _).
  intros X z. apply product_comma_factor_forget_injective.
  apply (@fp_encode_injective C P Q
    (costructured_source (structured_source X)) E).
  rewrite !product_comma_factor_encode. reflexivity.
Defined.

End SliceProductFamily.

Arguments product_slice_object {C P Q} E i.
Arguments product_comma_object {C P Q} E i.
Arguments product_comma_initial_family {C P Q} E.

