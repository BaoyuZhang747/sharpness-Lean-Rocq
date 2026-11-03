From DiazPark Require Import Category BarPaths.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A functor acts on the actual composable-arrow strings of the category bar.
    Every face, including the face changing the source, is preserved. *)
Module DPCategoryBarPullback.
Import DiazParkBarPaths.

Section MapPaths.
Variables C D : category.
Variable F : functor C D.

Fixpoint path_map_from (n : nat) :
    forall x, @path_from C n x -> @path_from D n (fobj F x) :=
  match n as k return forall x, @path_from C k x -> @path_from D k (fobj F x) with
  | O => fun _ _ => tt
  | S k => fun x p =>
      match p with
      | existT _ y (f,q) =>
          existT _ (fobj F y) (fmap F f, @path_map_from k y q)
      end
  end.

Arguments path_map_from _ _ _ : clear implicits.

Definition path_map n (p : @path C n) : @path D n :=
  match p with
  | existT _ x q => existT _ (fobj F x) (path_map_from n x q)
  end.

Arguments path_map _ _ : clear implicits.

Lemma path_map_inner_face n i x (p : @path_from C (S n) x) :
  path_map_from n x (@path_inner_face C n i x p) =
    @path_inner_face D n i (fobj F x) (path_map_from (S n) x p).
Proof.
  revert i x p. induction n as [|n IH]; intros i x p.
  - reflexivity.
  - destruct p as [y [f q]]. destruct i as [|i].
    + destruct q as [z [g r]]. simpl.
      rewrite fmap_compose. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

Lemma path_map_drop_first n (p : @path C (S n)) :
  path_map n (@path_drop_first C n p) =
    @path_drop_first D n (path_map (S n) p).
Proof. destruct p as [x [y [f q]]]. reflexivity. Qed.

Lemma path_map_remove_inner n i (p : @path C (S n)) :
  path_map n (@path_remove_inner C n i p) =
    @path_remove_inner D n i (path_map (S n) p).
Proof.
  destruct p as [x q]. unfold path_map, path_remove_inner.
  rewrite path_map_inner_face. reflexivity.
Qed.

Lemma path_map_face n i (p : @path C (S n)) :
  path_map n (@path_face C n i p) = @path_face D n i (path_map (S n) p).
Proof.
  destruct i; [apply path_map_drop_first | apply path_map_remove_inner].
Qed.

Lemma path_map_insert_identity n (p : @path C n) :
  path_map (S n) (@path_insert_identity C n p) =
    @path_insert_identity D n (path_map n p).
Proof.
  destruct p as [x q]. simpl. rewrite fmap_id. reflexivity.
Qed.

End MapPaths.

Arguments path_map_from {C D} F n x p.
Arguments path_map {C D} F n p.

Lemma path_map_from_identity (C : category) n x (p : @path_from C n x) :
  path_map_from (functor_id C) n x p = p.
Proof.
  revert x p. induction n as [|n IH]; intros x p.
  - destruct p. reflexivity.
  - destruct p as [y [f q]]. simpl. rewrite IH. reflexivity.
Qed.

Lemma path_map_identity (C : category) n (p : @path C n) :
  path_map (functor_id C) n p = p.
Proof.
  destruct p as [x q]. unfold path_map.
  rewrite path_map_from_identity. reflexivity.
Qed.

Lemma path_map_from_composition (C D E : category)
    (F : functor C D) (G : functor D E) n x (p : @path_from C n x) :
  path_map_from (functor_comp F G) n x p =
    path_map_from G n (fobj F x) (path_map_from F n x p).
Proof.
  revert x p. induction n as [|n IH]; intros x p.
  - reflexivity.
  - destruct p as [y [f q]]. simpl. rewrite IH. reflexivity.
Qed.

Lemma path_map_composition (C D E : category)
    (F : functor C D) (G : functor D E) n (p : @path C n) :
  path_map (functor_comp F G) n p = path_map G n (path_map F n p).
Proof.
  destruct p as [x q]. unfold path_map.
  rewrite path_map_from_composition. reflexivity.
Qed.

End DPCategoryBarPullback.
