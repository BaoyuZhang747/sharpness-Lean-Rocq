(** Pointwise left Kan extension from actual comma colimits, including
    arrow and coefficient functoriality. *)
From DiazPark Require Import Category CategoryExtensionality CategoryLimits
  CategoryColimitMaps CategoryComma.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition costructured_reindex_object {C D : category} (L : functor C D)
    {d e : D} (f : hom D d e) (X : costructured_category L d) : costructured_category L e :=
  @Build_costructured_object C D L e (costructured_source X) (compose (costructured_arrow X) f).

Arguments costructured_reindex_object {C D} L {d e} f X.

Definition costructured_reindex_map {C D : category} (L : functor C D)
    {d e : D} (f : hom D d e) {X Y : costructured_category L d}
    (u : hom (costructured_category L d) X Y) :
    hom (costructured_category L e) (costructured_reindex_object L f X) (costructured_reindex_object L f Y).
Proof.
refine (@Build_costructured_hom C D L e (costructured_reindex_object L f X) (costructured_reindex_object L f Y) (costructured_map u) _).
change (compose (fmap L (costructured_map u)) (compose (costructured_arrow Y) f) =
  compose (costructured_arrow X) f).
rewrite <- compose_assoc, costructured_commutes. reflexivity.
Defined.

Arguments costructured_reindex_map {C D} L {d e} f {X Y} u.

Definition costructured_identity_point {C D : category} (L : functor C D) (x : C) :
    costructured_category L (fobj L x) :=
  @Build_costructured_object C D L (fobj L x) x (identity (fobj L x)).

Section PointwiseLeftKan.
Context {C D E : category} (L : functor C D) (M : functor C E).
Variable K : forall d, colimiting_cocone (functor_comp (costructured_projection L d) M).

Definition lan_reindex_cocone {d e : D} (f : hom D d e) :
    cocone (functor_comp (costructured_projection L d) M) (colimit_object (K e)).
Proof.
refine (@Build_cocone (costructured_category L d) E (functor_comp (costructured_projection L d) M) (colimit_object (K e))
  (fun X => cocone_leg (colimit_cocone (K e)) (costructured_reindex_object L f X)) _).
intros X Y u. exact (cocone_natural (colimit_cocone (K e)) (costructured_reindex_map L f u)).
Defined.

Definition lan_arrow {d e : D} (f : hom D d e) : hom E (colimit_object (K d)) (colimit_object (K e)) :=
  colimit_desc (K d) (lan_reindex_cocone f).

Lemma lan_arrow_fac {d e : D} (f : hom D d e) (X : costructured_category L d) :
    compose (cocone_leg (colimit_cocone (K d)) X) (lan_arrow f) =
      cocone_leg (colimit_cocone (K e)) (costructured_reindex_object L f X).
Proof. exact (colimit_desc_fac (K d) (lan_reindex_cocone f) X). Qed.

Lemma lan_arrow_id d : lan_arrow (identity d) = identity (colimit_object (K d)).
Proof.
apply (colimit_hom_ext (K d)); intro X.
rewrite lan_arrow_fac, compose_id_right.
destruct X as [x h]. unfold costructured_reindex_object; simpl.
rewrite compose_id_right. reflexivity.
Qed.

Lemma lan_arrow_comp {d e k : D} (f : hom D d e) (g : hom D e k) :
    lan_arrow (compose f g) = compose (lan_arrow f) (lan_arrow g).
Proof.
apply (colimit_hom_ext (K d)); intro X.
transitivity (cocone_leg (colimit_cocone (K k))
  (costructured_reindex_object L g (costructured_reindex_object L f X))).
- rewrite lan_arrow_fac. destruct X as [x h].
  unfold costructured_reindex_object; simpl. rewrite compose_assoc. reflexivity.
- rewrite <- compose_assoc.
  transitivity (compose (cocone_leg (colimit_cocone (K e))
    (costructured_reindex_object L f X)) (lan_arrow g)).
  + symmetry; exact (lan_arrow_fac g (costructured_reindex_object L f X)).
  + rewrite (lan_arrow_fac f X). reflexivity.
Qed.

Definition pointwise_lan : functor D E.
Proof.
refine (@Build_functor D E (fun d => colimit_object (K d)) (fun d e f => lan_arrow f) _ _).
- exact lan_arrow_id.
- intros d e k f g; exact (lan_arrow_comp f g).
Defined.
End PointwiseLeftKan.

Arguments lan_arrow {C D E} L M K {d e} f.
Arguments lan_arrow_fac {C D E} L M K {d e} f X.
Arguments pointwise_lan {C D E} L M K.

Section CoefficientMaps.
Context {C D E : category} (L : functor C D) {M N : functor C E}.
Variable KM : forall d, colimiting_cocone (functor_comp (costructured_projection L d) M).
Variable KN : forall d, colimiting_cocone (functor_comp (costructured_projection L d) N).
Variable t : nat_trans M N.

Definition lan_coefficient_map d : hom E (colimit_object (KM d)) (colimit_object (KN d)) :=
  colimit_map (KM d) (KN d) (nat_whisker_left (costructured_projection L d) t).

Lemma lan_coefficient_map_fac d (X : costructured_category L d) :
    compose (cocone_leg (colimit_cocone (KM d)) X) (lan_coefficient_map d) =
      compose (component t (costructured_source X)) (cocone_leg (colimit_cocone (KN d)) X).
Proof. exact (colimit_map_fac (KM d) (KN d) (nat_whisker_left (costructured_projection L d) t) X). Qed.

Definition pointwise_lan_transform : nat_trans (pointwise_lan L M KM) (pointwise_lan L N KN).
Proof.
refine (@Build_nat_trans D E (pointwise_lan L M KM) (pointwise_lan L N KN) lan_coefficient_map _).
intros d e f. apply (colimit_hom_ext (KM d)); intro X.
change (compose (cocone_leg (colimit_cocone (KM d)) X)
  (compose (lan_arrow L M KM f) (lan_coefficient_map e)) =
  compose (cocone_leg (colimit_cocone (KM d)) X)
    (compose (lan_coefficient_map d) (lan_arrow L N KN f))).
rewrite <- !compose_assoc, lan_arrow_fac, !lan_coefficient_map_fac.
transitivity (compose (component t (costructured_source X))
  (cocone_leg (colimit_cocone (KN e)) (costructured_reindex_object L f X))).
- exact (@lan_coefficient_map_fac e (costructured_reindex_object L f X)).
- rewrite compose_assoc. apply f_equal. symmetry. exact (lan_arrow_fac L N KN f X).
Defined.
End CoefficientMaps.

Arguments lan_coefficient_map {C D E} L {M N} KM KN t d.
Arguments pointwise_lan_transform {C D E} L {M N} KM KN t.

Section LeftKanFunctor.
Context {C D E : category} (L : functor C D).
Variable K : forall (M : functor C E) d,
  colimiting_cocone (functor_comp (costructured_projection L d) M).

Definition pointwise_lan_functor : functor (functor_category C E) (functor_category D E).
Proof.
refine (@Build_functor (functor_category C E) (functor_category D E)
  (fun M => pointwise_lan L M (K M))
  (fun M N t => pointwise_lan_transform L (K M) (K N) t) _ _).
- intro M; apply nat_trans_ext; intro d.
  transitivity (colimit_map (K M d) (K M d) (nat_id (functor_comp (costructured_projection L d) M))).
  + apply colimit_map_congr; intro X; reflexivity.
  + apply colimit_map_id.
- intros M N O t u; apply nat_trans_ext; intro d.
  transitivity (colimit_map (K M d) (K O d)
    (nat_comp (nat_whisker_left (costructured_projection L d) t)
      (nat_whisker_left (costructured_projection L d) u))).
  + apply colimit_map_congr; intro X; reflexivity.
  + symmetry; apply colimit_map_comp.
Defined.
End LeftKanFunctor.
Arguments pointwise_lan_functor {C D E} L K.











