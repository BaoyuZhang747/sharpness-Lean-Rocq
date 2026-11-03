(** Reindexing along an essentially surjective object map, with the actual
    chosen isomorphisms. No strict inverse equality r(i(a)) = a is required. *)
From mathcomp Require Import all_boot.
From DiazPark Require Import Category CategoryReindex CategoryAdjunction.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPBLOReindexEquivalence.
Section Reindex.
Variable D : category.
Variable A : Type.
Variable i : A -> D.
Variable r : D -> A.
Variable e : forall x : D, @isomorphism D x (i (r x)).
Local Notation C := (reindexed_category D i).
Local Notation J := (reindex_inclusion D i).

Definition inverse_functor : functor D C.
Proof.
refine (@Build_functor D C r
  (fun x y f => compose (iso_inv (e x)) (compose f (iso_hom (e y)))) _ _).
- move=> x; change (compose (iso_inv (e x))
    (compose (@identity D x) (iso_hom (e x))) = @identity D (i (r x))).
  rewrite compose_id_left; exact: iso_inv_hom.
- move=> x y z f g.
  change (compose (iso_inv (e x)) (compose (compose f g) (iso_hom (e z))) =
    compose (compose (iso_inv (e x)) (compose f (iso_hom (e y))))
      (compose (iso_inv (e y)) (compose g (iso_hom (e z))))).
  by rewrite !compose_assoc -(compose_assoc (iso_hom (e y)) (iso_inv (e y)))
    iso_hom_inv compose_id_left.
Defined.

Lemma inverse_functor_object x : fobj inverse_functor x = r x.
Proof. reflexivity. Qed.

Lemma inverse_functor_map x y (f : hom D x y) :
    fmap inverse_functor f = compose (iso_inv (e x)) (compose f (iso_hom (e y))).
Proof. reflexivity. Qed.

Definition unit : nat_trans (functor_id C) (functor_comp J inverse_functor).
Proof.
refine (@Build_nat_trans C C (functor_id C) (functor_comp J inverse_functor)
  (fun a => iso_hom (e (i a))) _).
move=> a b f.
change (compose f (iso_hom (e (i b))) =
  compose (iso_hom (e (i a)))
    (compose (iso_inv (e (i a))) (compose f (iso_hom (e (i b)))))).
by rewrite -compose_assoc iso_hom_inv compose_id_left.
Defined.

Definition counit : nat_trans (functor_comp inverse_functor J) (functor_id D).
Proof.
refine (@Build_nat_trans D D (functor_comp inverse_functor J) (functor_id D)
  (fun x => iso_inv (e x)) _).
move=> x y f.
change (compose (compose (iso_inv (e x)) (compose f (iso_hom (e y))))
  (iso_inv (e y)) = compose (iso_inv (e x)) f).
by rewrite !compose_assoc iso_hom_inv compose_id_right.
Defined.

Lemma unit_component a : component unit a = iso_hom (e (i a)).
Proof. reflexivity. Qed.

Lemma counit_component x : component counit x = iso_inv (e x).
Proof. reflexivity. Qed.

Lemma triangle_left a :
    compose (fmap J (component unit a)) (component counit (fobj J a)) =
      identity (fobj J a).
Proof. exact: iso_hom_inv. Qed.

Lemma triangle_right x :
    compose (component unit (fobj inverse_functor x))
      (fmap inverse_functor (component counit x)) = identity (fobj inverse_functor x).
Proof.
change (compose (iso_hom (e (i (r x))))
  (compose (iso_inv (e (i (r x)))) (compose (iso_inv (e x)) (iso_hom (e x)))) =
  @identity D (i (r x))).
by rewrite -compose_assoc iso_hom_inv compose_id_left iso_inv_hom.
Qed.

Definition reindex_adjunction : adjunction J inverse_functor :=
  @Build_adjunction C D J inverse_functor unit counit triangle_left triangle_right.

Definition adjunction := reindex_adjunction.

Definition unit_iso (a : A) : @isomorphism C a (r (i a)).
Proof.
refine (@Build_isomorphism C a (r (i a)) (iso_hom (e (i a))) (iso_inv (e (i a))) _ _).
- exact (@iso_hom_inv D _ _ (e (i a))).
- exact (@iso_inv_hom D _ _ (e (i a))).
Defined.

Definition counit_iso (x : D) : @isomorphism D (i (r x)) x := iso_symm (e x).

Lemma unit_iso_hom a : iso_hom (unit_iso a) = component unit a.
Proof. reflexivity. Qed.

Lemma counit_iso_hom x : iso_hom (counit_iso x) = component counit x.
Proof. reflexivity. Qed.

End Reindex.
End DPBLOReindexEquivalence.
