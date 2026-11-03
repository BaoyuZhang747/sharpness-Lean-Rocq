(** Explicit incoming-arrow comma objects and their contravariant reindexing.
    This uses the actual structured category from CategoryComma. *)

From DiazPark Require Import Category CategoryComma.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition structured_point {C D : category} (L : functor C D) {d : D}
    (x : C) (f : hom D d (fobj L x)) : structured_category L d :=
  @Build_costructured_object (opposite C) (opposite D) (functor_op L) d x f.

Arguments structured_point {C D} L {d} x f.

Definition structured_source {C D : category} {L : functor C D} {d : D}
    (X : structured_category L d) : C := costructured_source X.

Definition structured_arrow {C D : category} {L : functor C D} {d : D}
    (X : structured_category L d) : hom D d (fobj L (structured_source X)) :=
  costructured_arrow X.

Definition structured_map {C D : category} {L : functor C D} {d : D}
    {X Y : structured_category L d} (f : hom (structured_category L d) X Y) :
    hom C (structured_source X) (structured_source Y) := costructured_map f.

Lemma structured_commutes {C D : category} {L : functor C D} {d : D}
    {X Y : structured_category L d} (f : hom (structured_category L d) X Y) :
    compose (structured_arrow X) (fmap L (structured_map f)) = structured_arrow Y.
Proof. exact (costructured_commutes f). Qed.

Definition structured_morphism {C D : category} {L : functor C D} {d : D}
    {X Y : structured_category L d}
    (f : hom C (structured_source X) (structured_source Y))
    (hf : compose (structured_arrow X) (fmap L f) = structured_arrow Y) :
    hom (structured_category L d) X Y :=
  @Build_costructured_hom (opposite C) (opposite D) (functor_op L) d Y X f hf.

Arguments structured_morphism {C D L d X Y} f hf.

Definition structured_reindex_object {C D : category} (L : functor C D)
    {d e : D} (f : hom D d e) (X : structured_category L e) : structured_category L d :=
  structured_point L (structured_source X) (compose f (structured_arrow X)).

Arguments structured_reindex_object {C D} L {d e} f X.

Definition structured_reindex_map {C D : category} (L : functor C D)
    {d e : D} (f : hom D d e) {X Y : structured_category L e}
    (u : hom (structured_category L e) X Y) :
    hom (structured_category L d)
      (structured_reindex_object L f X) (structured_reindex_object L f Y).
Proof.
  refine (@structured_morphism C D L d
    (structured_reindex_object L f X) (structured_reindex_object L f Y)
    (structured_map u) _).
  change (compose (compose f (structured_arrow X)) (fmap L (structured_map u)) =
    compose f (structured_arrow Y)).
  rewrite compose_assoc, structured_commutes. reflexivity.
Defined.

Arguments structured_reindex_map {C D} L {d e} f {X Y} u.

Definition structured_reindex {C D : category} (L : functor C D)
    {d e : D} (f : hom D d e) :
    functor (structured_category L e) (structured_category L d).
Proof.
  refine (@Build_functor (structured_category L e) (structured_category L d)
    (structured_reindex_object L f) (fun X Y u => structured_reindex_map L f u) _ _).
  - intro X. apply costructured_hom_ext. reflexivity.
  - intros X Y Z u v. apply costructured_hom_ext. reflexivity.
Defined.

Lemma structured_reindex_object_id {C D : category} (L : functor C D)
    (d : D) (X : structured_category L d) :
    structured_reindex_object L (identity d) X = X.
Proof.
  destruct X as [x h]. unfold structured_reindex_object, structured_point,
    structured_source, structured_arrow. simpl. rewrite compose_id_left. reflexivity.
Qed.

Lemma structured_reindex_object_comp {C D : category} (L : functor C D)
    {d e k : D} (f : hom D d e) (g : hom D e k) (X : structured_category L k) :
    structured_reindex_object L f (structured_reindex_object L g X) =
      structured_reindex_object L (compose f g) X.
Proof.
  destruct X as [x h]. unfold structured_reindex_object, structured_point,
    structured_source, structured_arrow. simpl. rewrite compose_assoc. reflexivity.
Qed.

Definition structured_identity_point {C D : category} (L : functor C D) (x : C) :
    structured_category L (fobj L x) := structured_point L x (identity (fobj L x)).
