(** Actual unit, counit and both triangle identities for the pointwise
    right Kan construction. Thus the comma-limit formula really is right
    adjoint to precomposition; the adjunction is not an assumed field. *)

From DiazPark Require Import Category CategoryExtensionality CategoryLimits
  CategoryLimitMaps CategoryAdjunction CategoryComma CategoryStructured CategoryRightKan.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RightKanAdjunction.
Context {C D E : category} (L : functor C D).
Variable K : forall (M : functor C E) d,
  limiting_cone (functor_comp (structured_projection L d) M).

Definition ran_unit_cone (H : functor D E) (d : D) :
    cone (functor_comp (structured_projection L d) (functor_comp L H)) (fobj H d).
Proof.
  refine (@Build_cone (structured_category L d) E
    (functor_comp (structured_projection L d) (functor_comp L H)) (fobj H d)
    (fun X => fmap H (structured_arrow X)) _).
  intros X Y u.
  change (compose (fmap H (structured_arrow X)) (fmap H (fmap L (structured_map u))) =
    fmap H (structured_arrow Y)).
  rewrite <- fmap_compose. apply f_equal. exact (structured_commutes u).
Defined.

Definition ran_unit_component (H : functor D E) (d : D) :
    hom E (fobj H d) (limit_object (K (functor_comp L H) d)) :=
  limit_lift (K (functor_comp L H) d) (ran_unit_cone H d).

Lemma ran_unit_component_fac (H : functor D E) (d : D)
    (X : structured_category L d) :
    compose (ran_unit_component H d)
      (cone_leg (limit_cone (K (functor_comp L H) d)) X) = fmap H (structured_arrow X).
Proof. exact (limit_lift_fac (K (functor_comp L H) d) (ran_unit_cone H d) X). Qed.

Definition ran_unit_object (H : functor D E) :
    nat_trans H (pointwise_ran L (functor_comp L H) (K (functor_comp L H))).
Proof.
  refine (@Build_nat_trans D E H
    (pointwise_ran L (functor_comp L H) (K (functor_comp L H)))
    (ran_unit_component H) _).
  intros d e f. apply (limit_hom_ext (K (functor_comp L H) e)). intro X.
  change (compose (compose (fmap H f) (ran_unit_component H e))
      (cone_leg (limit_cone (K (functor_comp L H) e)) X) =
    compose (compose (ran_unit_component H d)
      (ran_arrow L (functor_comp L H) (K (functor_comp L H)) f))
      (cone_leg (limit_cone (K (functor_comp L H) e)) X)).
  rewrite !compose_assoc, ran_unit_component_fac,
    (ran_arrow_fac L (functor_comp L H) (K (functor_comp L H)) f X).
  transitivity (fmap H (compose f (structured_arrow X))).
  - symmetry. exact (fmap_compose H f (structured_arrow X)).
  - symmetry. exact (ran_unit_component_fac H (structured_reindex_object L f X)).
Defined.

Definition ran_unit :
    nat_trans (functor_id (functor_category D E))
      (functor_comp (precomposition E L) (pointwise_ran_functor L K)).
Proof.
  refine (@Build_nat_trans (functor_category D E) (functor_category D E)
    (functor_id (functor_category D E))
    (functor_comp (precomposition E L) (pointwise_ran_functor L K)) ran_unit_object _).
  intros H J t. apply nat_trans_ext. intro d.
  apply (limit_hom_ext (K (functor_comp L J) d)). intro X.
  change (compose (compose (component t d) (ran_unit_component J d))
      (cone_leg (limit_cone (K (functor_comp L J) d)) X) =
    compose (compose (ran_unit_component H d)
      (ran_coefficient_map L (K (functor_comp L H)) (K (functor_comp L J))
        (nat_whisker_left L t) d))
      (cone_leg (limit_cone (K (functor_comp L J) d)) X)).
  rewrite !compose_assoc, ran_unit_component_fac.
  rewrite (@ran_coefficient_map_fac C D E L (functor_comp L H) (functor_comp L J)
    (K (functor_comp L H)) (K (functor_comp L J)) (nat_whisker_left L t) d X).
  rewrite <- compose_assoc, ran_unit_component_fac.
  symmetry. exact (naturality t (structured_arrow X)).
Defined.

Definition ran_counit_component (M : functor C E) (x : C) :
    hom E (limit_object (K M (fobj L x))) (fobj M x) :=
  cone_leg (limit_cone (K M (fobj L x))) (structured_identity_point L x).

Definition ran_counit_index_arrow {x y : C} (f : hom C x y) :
    hom (structured_category L (fobj L x)) (structured_identity_point L x)
      (structured_reindex_object L (fmap L f) (structured_identity_point L y)).
Proof.
  refine (@structured_morphism C D L (fobj L x) (structured_identity_point L x)
    (structured_reindex_object L (fmap L f) (structured_identity_point L y)) f _).
  change (compose (identity (fobj L x)) (fmap L f) =
    compose (fmap L f) (identity (fobj L y))).
  rewrite compose_id_left, compose_id_right. reflexivity.
Defined.

Definition ran_counit_object (M : functor C E) :
    nat_trans (functor_comp L (pointwise_ran L M (K M))) M.
Proof.
  refine (@Build_nat_trans C E (functor_comp L (pointwise_ran L M (K M))) M
    (ran_counit_component M) _).
  intros x y f.
  change (compose (ran_arrow L M (K M) (fmap L f))
    (cone_leg (limit_cone (K M (fobj L y))) (structured_identity_point L y)) =
    compose (ran_counit_component M x) (fmap M f)).
  rewrite ran_arrow_fac.
  symmetry. exact (cone_natural (limit_cone (K M (fobj L x))) (ran_counit_index_arrow f)).
Defined.

Definition ran_counit :
    nat_trans (functor_comp (pointwise_ran_functor L K) (precomposition E L))
      (functor_id (functor_category C E)).
Proof.
  refine (@Build_nat_trans (functor_category C E) (functor_category C E)
    (functor_comp (pointwise_ran_functor L K) (precomposition E L))
    (functor_id (functor_category C E)) ran_counit_object _).
  intros M N t. apply nat_trans_ext. intro x.
  exact (@ran_coefficient_map_fac C D E L M N (K M) (K N) t
    (fobj L x) (structured_identity_point L x)).
Defined.

Definition pointwise_ran_adjunction :
    adjunction (precomposition E L) (pointwise_ran_functor L K).
Proof.
  refine (@Build_adjunction (functor_category D E) (functor_category C E)
    (precomposition E L) (pointwise_ran_functor L K) ran_unit ran_counit _ _).
  - intro H. apply nat_trans_ext. intro x.
    change (compose (ran_unit_component H (fobj L x))
      (cone_leg (limit_cone (K (functor_comp L H) (fobj L x)))
        (structured_identity_point L x)) = identity (fobj H (fobj L x))).
    rewrite ran_unit_component_fac. exact (fmap_id H (fobj L x)).
  - intro M. apply nat_trans_ext. intro d.
    apply (limit_hom_ext (K M d)). intro X.
    change (compose
      (compose (ran_unit_component (pointwise_ran L M (K M)) d)
        (ran_coefficient_map L
          (K (functor_comp L (pointwise_ran L M (K M)))) (K M)
          (ran_counit_object M) d)) (cone_leg (limit_cone (K M d)) X) =
      compose (identity (limit_object (K M d))) (cone_leg (limit_cone (K M d)) X)).
    rewrite compose_assoc, compose_id_left.
    rewrite (@ran_coefficient_map_fac C D E L
      (functor_comp L (pointwise_ran L M (K M))) M
      (K (functor_comp L (pointwise_ran L M (K M)))) (K M)
      (ran_counit_object M) d X).
    rewrite <- compose_assoc, ran_unit_component_fac.
    change (compose (ran_arrow L M (K M) (structured_arrow X))
      (cone_leg (limit_cone (K M (fobj L (structured_source X))))
        (structured_identity_point L (structured_source X))) =
      cone_leg (limit_cone (K M d)) X).
    rewrite ran_arrow_fac.
    destruct X as [x h].
    change (cone_leg (limit_cone (K M d))
      (structured_point L x (@compose D d (fobj L x) (fobj L x) h (identity (fobj L x)))) =
      cone_leg (limit_cone (K M d)) (structured_point L x h)).
    rewrite compose_id_right. reflexivity.
Defined.

End RightKanAdjunction.

Arguments pointwise_ran_adjunction {C D E} L K.
