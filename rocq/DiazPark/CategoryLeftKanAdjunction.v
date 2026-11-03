(** Actual unit, counit and triangles for pointwise left Kan extension. *)
From DiazPark Require Import Category CategoryExtensionality CategoryLimits
  CategoryColimitMaps CategoryAdjunction CategoryComma CategoryLeftKan.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LeftKanAdjunction.
Context {C D E : category} (L : functor C D).
Variable K : forall (M : functor C E) d,
  colimiting_cocone (functor_comp (costructured_projection L d) M).

Definition lan_unit_component (M : functor C E) x :
    hom E (fobj M x) (colimit_object (K M (fobj L x))) :=
  cocone_leg (colimit_cocone (K M (fobj L x))) (costructured_identity_point L x).

Definition lan_unit_index_arrow {x y : C} (f : hom C x y) :
    hom (costructured_category L (fobj L y))
      (costructured_reindex_object L (fmap L f) (costructured_identity_point L x))
      (costructured_identity_point L y).
Proof.
refine (@Build_costructured_hom C D L (fobj L y)
  (costructured_reindex_object L (fmap L f) (costructured_identity_point L x))
  (costructured_identity_point L y) f _).
change (compose (fmap L f) (identity (fobj L y)) = compose (identity (fobj L x)) (fmap L f)).
rewrite compose_id_left, compose_id_right. reflexivity.
Defined.

Definition lan_unit_object (M : functor C E) :
    nat_trans M (functor_comp L (pointwise_lan L M (K M))).
Proof.
refine (@Build_nat_trans C E M (functor_comp L (pointwise_lan L M (K M))) (lan_unit_component M) _).
intros x y f.
change (compose (fmap M f) (lan_unit_component M y) =
  compose (cocone_leg (colimit_cocone (K M (fobj L x))) (costructured_identity_point L x))
    (lan_arrow L M (K M) (fmap L f))).
rewrite lan_arrow_fac. exact (cocone_natural (colimit_cocone (K M (fobj L y))) (lan_unit_index_arrow f)).
Defined.

Definition lan_unit : nat_trans (functor_id (functor_category C E))
    (functor_comp (pointwise_lan_functor L K) (precomposition E L)).
Proof.
refine (@Build_nat_trans (functor_category C E) (functor_category C E)
  (functor_id _) (functor_comp (pointwise_lan_functor L K) (precomposition E L)) lan_unit_object _).
intros M N t; apply nat_trans_ext; intro x.
symmetry. exact (@lan_coefficient_map_fac C D E L M N (K M) (K N) t
  (fobj L x) (costructured_identity_point L x)).
Defined.

Definition lan_counit_cocone (H : functor D E) d :
    cocone (functor_comp (costructured_projection L d) (functor_comp L H)) (fobj H d).
Proof.
refine (@Build_cocone (costructured_category L d) E
  (functor_comp (costructured_projection L d) (functor_comp L H)) (fobj H d)
  (fun X => fmap H (costructured_arrow X)) _).
intros X Y u.
change (compose (fmap H (fmap L (costructured_map u))) (fmap H (costructured_arrow Y)) =
  fmap H (costructured_arrow X)).
rewrite <- fmap_compose, costructured_commutes. reflexivity.
Defined.

Definition lan_counit_component (H : functor D E) d :
    hom E (colimit_object (K (functor_comp L H) d)) (fobj H d) :=
  colimit_desc (K (functor_comp L H) d) (lan_counit_cocone H d).

Lemma lan_counit_component_fac (H : functor D E) d (X : costructured_category L d) :
    compose (cocone_leg (colimit_cocone (K (functor_comp L H) d)) X)
      (lan_counit_component H d) = fmap H (costructured_arrow X).
Proof. exact (colimit_desc_fac (K (functor_comp L H) d) (lan_counit_cocone H d) X). Qed.

Definition lan_counit_object (H : functor D E) :
    nat_trans (pointwise_lan L (functor_comp L H) (K (functor_comp L H))) H.
Proof.
refine (@Build_nat_trans D E (pointwise_lan L (functor_comp L H) (K (functor_comp L H))) H (lan_counit_component H) _).
intros d e f. apply (colimit_hom_ext (K (functor_comp L H) d)); intro X.
change (compose (cocone_leg (colimit_cocone (K (functor_comp L H) d)) X)
  (compose (lan_arrow L (functor_comp L H) (K (functor_comp L H)) f) (lan_counit_component H e)) =
  compose (cocone_leg (colimit_cocone (K (functor_comp L H) d)) X)
    (compose (lan_counit_component H d) (fmap H f))).
rewrite <- !compose_assoc.
rewrite (lan_arrow_fac L (functor_comp L H) (K (functor_comp L H)) f X).
transitivity (fmap H (compose (costructured_arrow X) f)).
- exact (@lan_counit_component_fac H e (costructured_reindex_object L f X)).
- transitivity (compose (fmap H (costructured_arrow X)) (fmap H f)).
  + exact (fmap_compose H (costructured_arrow X) f).
  + apply f_equal2; [symmetry; exact (@lan_counit_component_fac H d X) | reflexivity].
Defined.

Definition lan_counit : nat_trans
    (functor_comp (precomposition E L) (pointwise_lan_functor L K))
    (functor_id (functor_category D E)).
Proof.
refine (@Build_nat_trans (functor_category D E) (functor_category D E)
  (functor_comp (precomposition E L) (pointwise_lan_functor L K)) (functor_id _) lan_counit_object _).
intros H J t; apply nat_trans_ext; intro d.
apply (colimit_hom_ext (K (functor_comp L H) d)); intro X.
change (compose (cocone_leg (colimit_cocone (K (functor_comp L H) d)) X)
  (compose (lan_coefficient_map L (K (functor_comp L H)) (K (functor_comp L J))
    (nat_whisker_left L t) d) (lan_counit_component J d)) =
  compose (cocone_leg (colimit_cocone (K (functor_comp L H) d)) X)
    (compose (lan_counit_component H d) (component t d))).
rewrite <- !compose_assoc.
rewrite (@lan_coefficient_map_fac C D E L (functor_comp L H) (functor_comp L J)
  (K (functor_comp L H)) (K (functor_comp L J)) (nat_whisker_left L t) d X).
transitivity (compose (component t (fobj L (costructured_source X))) (fmap J (costructured_arrow X))).
- rewrite compose_assoc. apply f_equal. exact (@lan_counit_component_fac J d X).
- transitivity (compose (fmap H (costructured_arrow X)) (component t d)).
  + symmetry; exact (naturality t (costructured_arrow X)).
  + apply f_equal2; [symmetry; exact (@lan_counit_component_fac H d X) | reflexivity].
Defined.

Definition pointwise_lan_adjunction : adjunction (pointwise_lan_functor L K) (precomposition E L).
Proof.
refine (@Build_adjunction (functor_category C E) (functor_category D E)
  (pointwise_lan_functor L K) (precomposition E L) lan_unit lan_counit _ _).
- intro M; apply nat_trans_ext; intro d; apply (colimit_hom_ext (K M d)); intro X.
  change (compose (cocone_leg (colimit_cocone (K M d)) X)
    (compose (lan_coefficient_map L (K M)
      (K (functor_comp L (pointwise_lan L M (K M)))) (lan_unit_object M) d)
      (lan_counit_component (pointwise_lan L M (K M)) d)) =
    compose (cocone_leg (colimit_cocone (K M d)) X) (identity (colimit_object (K M d)))).
  rewrite compose_id_right, <- compose_assoc.
  rewrite (@lan_coefficient_map_fac C D E L M (functor_comp L (pointwise_lan L M (K M)))
    (K M) (K (functor_comp L (pointwise_lan L M (K M)))) (lan_unit_object M) d X).
  transitivity (compose (component (lan_unit_object M) (costructured_source X))
    (fmap (pointwise_lan L M (K M)) (costructured_arrow X))).
  + rewrite compose_assoc. apply f_equal. exact (@lan_counit_component_fac (pointwise_lan L M (K M)) d X).
  +
  change (compose (cocone_leg (colimit_cocone (K M (fobj L (costructured_source X))))
    (costructured_identity_point L (costructured_source X)))
    (lan_arrow L M (K M) (costructured_arrow X)) = cocone_leg (colimit_cocone (K M d)) X).
  rewrite lan_arrow_fac. destruct X as [x h].
  unfold costructured_reindex_object, costructured_identity_point; simpl.
  rewrite compose_id_left. reflexivity.
- intro H; apply nat_trans_ext; intro x.
  change (compose (cocone_leg (colimit_cocone (K (functor_comp L H) (fobj L x)))
    (costructured_identity_point L x)) (lan_counit_component H (fobj L x)) =
    identity (fobj H (fobj L x))).
  transitivity (fmap H (identity (fobj L x))).
  + exact (@lan_counit_component_fac H (fobj L x) (costructured_identity_point L x)).
  + exact (fmap_id H (fobj L x)).
Defined.
End LeftKanAdjunction.
Arguments pointwise_lan_adjunction {C D E} L K.






