(** Ordinary limits commute with the constructed right Kan extension.
    The cone correspondence and its universal properties are proved
    explicitly; no derived comparison is asserted here. *)
From DiazPark Require Import Category CategoryLimits CategoryLimitMaps
  CategoryComma CategoryStructured CategoryRightKan CategoryRightKanAdjunction.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section RanLimits.
Context {C D E : category} (L : functor C D) (M : functor C E).
Variable K : forall d, limiting_cone (functor_comp (structured_projection L d) M).

Definition ran_limit_comma_cone {v : E} (s : cone M v) (d : D) :
    cone (functor_comp (structured_projection L d) M) v.
Proof.
  refine (@Build_cone (structured_category L d) E
    (functor_comp (structured_projection L d) M) v
    (fun X => cone_leg s (structured_source X)) _).
  intros X Y f. exact (cone_natural s (structured_map f)).
Defined.

Definition ran_limit_extend {v : E} (s : cone M v) :
    cone (pointwise_ran L M K) v.
Proof.
  refine (@Build_cone D E (pointwise_ran L M K) v
    (fun d => limit_lift (K d) (ran_limit_comma_cone s d)) _).
  intros d e f. apply (limit_hom_ext (K e)). intro X.
  change (compose
    (compose (limit_lift (K d) (ran_limit_comma_cone s d)) (ran_arrow L M K f))
    (cone_leg (limit_cone (K e)) X) =
    compose (limit_lift (K e) (ran_limit_comma_cone s e))
    (cone_leg (limit_cone (K e)) X)).
  rewrite compose_assoc, ran_arrow_fac.
  transitivity (cone_leg s (structured_source X)).
  - exact (limit_lift_fac (K d) (ran_limit_comma_cone s d)
      (structured_reindex_object L f X)).
  - symmetry. exact (limit_lift_fac (K e) (ran_limit_comma_cone s e) X).
Defined.

Lemma ran_limit_extend_coordinate {v : E} (s : cone M v) d
    (X : structured_category L d) :
    compose (cone_leg (ran_limit_extend s) d) (cone_leg (limit_cone (K d)) X) =
      cone_leg s (structured_source X).
Proof. exact (limit_lift_fac (K d) (ran_limit_comma_cone s d) X). Qed.

Definition ran_limit_restrict {v : E} (s : cone (pointwise_ran L M K) v) : cone M v.
Proof.
  refine (@Build_cone C E M v
    (fun x => compose (cone_leg s (fobj L x))
      (cone_leg (limit_cone (K (fobj L x))) (structured_identity_point L x))) _).
  intros x y f. rewrite compose_assoc.
  transitivity (compose (cone_leg s (fobj L x))
    (cone_leg (limit_cone (K (fobj L x)))
      (structured_reindex_object L (fmap L f) (structured_identity_point L y)))).
  - apply f_equal. exact (cone_natural (limit_cone (K (fobj L x)))
      (ran_counit_index_arrow L f)).
  - rewrite <- (ran_arrow_fac L M K (fmap L f) (structured_identity_point L y)).
    rewrite <- compose_assoc.
    apply f_equal2; [exact (cone_natural s (fmap L f)) | reflexivity].
Defined.

Lemma ran_arrow_identity_coordinate (d : D) (X : structured_category L d) :
    compose (ran_arrow L M K (structured_arrow X))
      (cone_leg (limit_cone (K (fobj L (structured_source X))))
        (structured_identity_point L (structured_source X))) =
      cone_leg (limit_cone (K d)) X.
Proof.
  rewrite ran_arrow_fac. destruct X as [x h].
  change (cone_leg (limit_cone (K d))
    (structured_point L x (@compose D d (fobj L x) (fobj L x)
      h (identity (fobj L x)))) =
    cone_leg (limit_cone (K d)) (structured_point L x h)).
  rewrite compose_id_right. reflexivity.
Qed.

Lemma ran_limit_restrict_coordinate {v : E}
    (s : cone (pointwise_ran L M K) v) d (X : structured_category L d) :
    cone_leg (ran_limit_restrict s) (structured_source X) =
      compose (cone_leg s d) (cone_leg (limit_cone (K d)) X).
Proof.
  change (compose (cone_leg s (fobj L (structured_source X)))
    (cone_leg (limit_cone (K (fobj L (structured_source X))))
      (structured_identity_point L (structured_source X))) =
    compose (cone_leg s d) (cone_leg (limit_cone (K d)) X)).
  rewrite <- (cone_natural s (structured_arrow X)), compose_assoc.
  apply f_equal. exact (ran_arrow_identity_coordinate X).
Qed.

Definition ran_limit (J : limiting_cone M) : limiting_cone (pointwise_ran L M K).
Proof.
  refine (@Build_limiting_cone D E (pointwise_ran L M K)
    (limit_object J) (ran_limit_extend (limit_cone J))
    (fun v s => limit_lift J (ran_limit_restrict s)) _ _).
  - intros v s d. apply (limit_hom_ext (K d)). intro X.
    change (compose
      (compose (limit_lift J (ran_limit_restrict s))
        (cone_leg (ran_limit_extend (limit_cone J)) d))
      (cone_leg (limit_cone (K d)) X) =
      compose (cone_leg s d) (cone_leg (limit_cone (K d)) X)).
    rewrite compose_assoc.
    transitivity (compose (limit_lift J (ran_limit_restrict s))
      (cone_leg (limit_cone J) (structured_source X))).
    + apply f_equal. exact (ran_limit_extend_coordinate (limit_cone J) X).
    + rewrite limit_lift_fac. exact (ran_limit_restrict_coordinate s X).
  - intros v s f hf. apply limit_lift_unique. intro x.
    transitivity (compose f
      (compose (cone_leg (ran_limit_extend (limit_cone J)) (fobj L x))
        (cone_leg (limit_cone (K (fobj L x))) (structured_identity_point L x)))).
    + rewrite ran_limit_extend_coordinate. reflexivity.
    + rewrite <- compose_assoc, (hf (fobj L x)). reflexivity.
Defined.

Definition right_kan_limit_iso (J : limiting_cone M)
    (I : limiting_cone (pointwise_ran L M K)) :
    isomorphism (limit_object I) (limit_object J) :=
  limit_unique_iso I (ran_limit J).

Lemma right_kan_limit_iso_coordinate (J : limiting_cone M)
    (I : limiting_cone (pointwise_ran L M K)) (x : C) :
    compose (iso_hom (right_kan_limit_iso J I)) (cone_leg (limit_cone J) x) =
      compose (cone_leg (limit_cone I) (fobj L x))
        (cone_leg (limit_cone (K (fobj L x))) (structured_identity_point L x)).
Proof.
  change (compose
    (limit_lift J (ran_limit_restrict (cone_map (nat_id (pointwise_ran L M K))
      (limit_cone I)))) (cone_leg (limit_cone J) x) =
    compose (cone_leg (limit_cone I) (fobj L x))
      (cone_leg (limit_cone (K (fobj L x))) (structured_identity_point L x))).
  rewrite limit_lift_fac. simpl.
  rewrite compose_id_right. reflexivity.
Qed.
End RanLimits.

Arguments ran_limit {C D E} L M K J.
Arguments right_kan_limit_iso {C D E} L M K J I.

Lemma right_kan_limit_iso_natural {C D E : category}
    (L : functor C D) {M N : functor C E}
    (KM : forall d, limiting_cone (functor_comp (structured_projection L d) M))
    (KN : forall d, limiting_cone (functor_comp (structured_projection L d) N))
    (JM : limiting_cone M) (JN : limiting_cone N)
    (IM : limiting_cone (pointwise_ran L M KM))
    (IN : limiting_cone (pointwise_ran L N KN)) (t : nat_trans M N) :
    compose (limit_map IM IN (pointwise_ran_transform L KM KN t))
      (iso_hom (right_kan_limit_iso L N KN JN IN)) =
    compose (iso_hom (right_kan_limit_iso L M KM JM IM)) (limit_map JM JN t).
Proof.
  apply (limit_hom_ext JN). intro x.
  rewrite compose_assoc.
  rewrite (@right_kan_limit_iso_coordinate C D E L N KN JN IN x).
  rewrite <- compose_assoc, limit_map_fac.
  change (compose
    (compose (cone_leg (limit_cone IM) (fobj L x))
      (ran_coefficient_map L KM KN t (fobj L x)))
    (cone_leg (limit_cone (KN (fobj L x))) (structured_identity_point L x)) =
    compose (compose (iso_hom (right_kan_limit_iso L M KM JM IM))
      (limit_map JM JN t)) (cone_leg (limit_cone JN) x)).
  rewrite compose_assoc.
  transitivity (compose (cone_leg (limit_cone IM) (fobj L x))
    (compose (cone_leg (limit_cone (KM (fobj L x))) (structured_identity_point L x))
      (component t x))).
  - apply f_equal. exact (@ran_coefficient_map_fac C D E L M N KM KN t
      (fobj L x) (structured_identity_point L x)).
  - rewrite <- compose_assoc.
    rewrite <- (@right_kan_limit_iso_coordinate C D E L M KM JM IM x).
    rewrite !compose_assoc, limit_map_fac. reflexivity.
Qed.
