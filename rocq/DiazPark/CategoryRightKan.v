(** The pointwise right Kan construction from actual incoming-comma limits.
    This file constructs its object, arrow and coefficient functoriality.
    The precomposition adjunction is proved separately. *)

From DiazPark Require Import Category CategoryExtensionality CategoryLimits
  CategoryLimitMaps CategoryComma CategoryStructured.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PointwiseRightKan.
Context {C D E : category} (L : functor C D) (M : functor C E).
Variable K : forall d, limiting_cone (functor_comp (structured_projection L d) M).

Definition ran_reindex_cone {d e : D} (f : hom D d e) :
    cone (functor_comp (structured_projection L e) M) (limit_object (K d)).
Proof.
  refine (@Build_cone (structured_category L e) E
    (functor_comp (structured_projection L e) M) (limit_object (K d))
    (fun X => cone_leg (limit_cone (K d)) (structured_reindex_object L f X)) _).
  intros X Y u. exact (cone_natural (limit_cone (K d)) (structured_reindex_map L f u)).
Defined.

Definition ran_arrow {d e : D} (f : hom D d e) :
    hom E (limit_object (K d)) (limit_object (K e)) :=
  limit_lift (K e) (ran_reindex_cone f).

Lemma ran_arrow_fac {d e : D} (f : hom D d e) (X : structured_category L e) :
    compose (ran_arrow f) (cone_leg (limit_cone (K e)) X) =
      cone_leg (limit_cone (K d)) (structured_reindex_object L f X).
Proof. exact (limit_lift_fac (K e) (ran_reindex_cone f) X). Qed.

Lemma ran_arrow_id d : ran_arrow (identity d) = identity (limit_object (K d)).
Proof.
  apply (limit_hom_ext (K d)). intro X.
  rewrite ran_arrow_fac, compose_id_left.
  destruct X as [x h].
  change (cone_leg (limit_cone (K d)) (structured_point L x (compose (identity d) h)) =
    cone_leg (limit_cone (K d)) (structured_point L x h)).
  rewrite compose_id_left. reflexivity.
Qed.

Lemma ran_arrow_comp {d e k : D} (f : hom D d e) (g : hom D e k) :
    ran_arrow (compose f g) = compose (ran_arrow f) (ran_arrow g).
Proof.
  apply (limit_hom_ext (K k)). intro X.
  rewrite compose_assoc, !ran_arrow_fac.
  transitivity (cone_leg (limit_cone (K d))
    (structured_reindex_object L f (structured_reindex_object L g X))).
  - destruct X as [x h].
    change (cone_leg (limit_cone (K d)) (structured_point L x (compose (compose f g) h)) =
      cone_leg (limit_cone (K d)) (structured_point L x (compose f (compose g h)))).
    rewrite compose_assoc. reflexivity.
  - symmetry. exact (ran_arrow_fac f (structured_reindex_object L g X)).
Qed.

Definition pointwise_ran : functor D E.
Proof.
  refine (@Build_functor D E (fun d => limit_object (K d))
    (fun d e f => ran_arrow f) _ _).
  - exact ran_arrow_id.
  - intros d e k f g. exact (ran_arrow_comp f g).
Defined.

End PointwiseRightKan.

Arguments ran_arrow {C D E} L M K {d e} f.
Arguments ran_arrow_fac {C D E} L M K {d e} f X.
Arguments pointwise_ran {C D E} L M K.

Section CoefficientMaps.
Context {C D E : category} (L : functor C D).
Context {M N : functor C E}.
Variable KM : forall d, limiting_cone (functor_comp (structured_projection L d) M).
Variable KN : forall d, limiting_cone (functor_comp (structured_projection L d) N).
Variable t : nat_trans M N.

Definition ran_coefficient_map (d : D) :
    hom E (limit_object (KM d)) (limit_object (KN d)) :=
  limit_map (KM d) (KN d) (nat_whisker_left (structured_projection L d) t).

Lemma ran_coefficient_map_fac (d : D) (X : structured_category L d) :
    compose (ran_coefficient_map d) (cone_leg (limit_cone (KN d)) X) =
      compose (cone_leg (limit_cone (KM d)) X) (component t (structured_source X)).
Proof. exact (limit_map_fac (KM d) (KN d)
  (nat_whisker_left (structured_projection L d) t) X). Qed.

Definition pointwise_ran_transform :
    nat_trans (pointwise_ran L M KM) (pointwise_ran L N KN).
Proof.
  refine (@Build_nat_trans D E (pointwise_ran L M KM) (pointwise_ran L N KN)
    ran_coefficient_map _).
  intros d e f. apply (limit_hom_ext (KN e)). intro X.
  change (compose (compose (ran_arrow L M KM f) (ran_coefficient_map e))
      (cone_leg (limit_cone (KN e)) X) =
    compose (compose (ran_coefficient_map d) (ran_arrow L N KN f))
      (cone_leg (limit_cone (KN e)) X)).
  rewrite !compose_assoc, ran_coefficient_map_fac, (ran_arrow_fac L N KN f X).
  rewrite <- compose_assoc, (ran_arrow_fac L M KM f X).
  symmetry. exact (ran_coefficient_map_fac (structured_reindex_object L f X)).
Defined.

End CoefficientMaps.

Arguments ran_coefficient_map {C D E} L {M N} KM KN t d.
Arguments pointwise_ran_transform {C D E} L {M N} KM KN t.

Section RightKanFunctor.
Context {C D E : category} (L : functor C D).
Variable K : forall (M : functor C E) d,
  limiting_cone (functor_comp (structured_projection L d) M).

Definition pointwise_ran_functor :
    functor (functor_category C E) (functor_category D E).
Proof.
  refine (@Build_functor (functor_category C E) (functor_category D E)
    (fun M => pointwise_ran L M (K M))
    (fun M N t => pointwise_ran_transform L (K M) (K N) t) _ _).
  - intro M. apply nat_trans_ext. intro d.
    transitivity (limit_map (K M d) (K M d)
      (nat_id (functor_comp (structured_projection L d) M))).
    + apply limit_map_congr. intro X. reflexivity.
    + apply limit_map_id.
  - intros M N P t u. apply nat_trans_ext. intro d.
    change (limit_map (K M d) (K P d)
      (nat_whisker_left (structured_projection L d) (nat_comp t u)) =
      compose
        (limit_map (K M d) (K N d) (nat_whisker_left (structured_projection L d) t))
        (limit_map (K N d) (K P d) (nat_whisker_left (structured_projection L d) u))).
    rewrite limit_map_comp. apply limit_map_congr. intro X. reflexivity.
Defined.

End RightKanFunctor.

Arguments pointwise_ran_functor {C D E} L K.
