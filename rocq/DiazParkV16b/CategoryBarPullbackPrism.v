From Stdlib Require Import Lia.
From DiazPark Require Import Category BarPaths.
From DiazParkV16b Require Import CategoryBarPullbackPaths.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The actual prism of a natural transformation on composable-arrow strings.
    Position i follows F for i arrows, uses alpha, then follows G. *)
Module DPCategoryBarPrism.
Import DiazParkBarPaths DPCategoryBarPullback.

Section Prism.
Variables C D : category.
Variables F G : functor C D.
Variable alpha : nat_trans F G.

Fixpoint path_prism_from (n : nat) :
    forall i x, @path_from C n x -> @path_from D (S n) (fobj F x) :=
  match n as k return forall i x, @path_from C k x -> @path_from D (S k) (fobj F x) with
  | O => fun _ x _ => existT _ (fobj G x) (component alpha x,tt)
  | S k => fun i x p =>
      match i with
      | O => existT _ (fobj G x) (component alpha x,path_map_from G (S k) x p)
      | S j => match p with
        | existT _ y (f,q) =>
          existT _ (fobj F y) (fmap F f,@path_prism_from k j y q)
        end
      end
  end.

Arguments path_prism_from n i x p : clear implicits.

Definition path_prism n i (p : @path C n) : @path D (S n) :=
  match p with
  | existT _ x q => existT _ (fobj F x) (path_prism_from n i x q)
  end.

Arguments path_prism n i p : clear implicits.

Lemma path_prism_from_zero n x (p : @path_from C n x) :
  path_prism_from n 0 x p =
    existT _ (fobj G x) (component alpha x,path_map_from G n x p).
Proof. destruct n; reflexivity. Qed.

Lemma path_prism_first_face n (p : @path C n) :
  @path_face D n 0 (path_prism n 0 p) = path_map G n p.
Proof.
  destruct p as [x q]. unfold path_prism.
  rewrite path_prism_from_zero. reflexivity.
Qed.

Lemma path_prism_last_inner n x (p : @path_from C n x) :
  @path_inner_face D n n (fobj F x) (path_prism_from n n x p) =
    path_map_from F n x p.
Proof.
  revert x p. induction n as [|n IH]; intros x p.
  - reflexivity.
  - destruct p as [y [f q]]. simpl. rewrite IH. reflexivity.
Qed.

Lemma path_prism_last_face n (p : @path C n) :
  @path_face D n (S n) (path_prism n n p) = path_map F n p.
Proof.
  destruct p as [x q]. unfold path_prism, path_face, path_remove_inner, path_map.
  rewrite path_prism_last_inner. reflexivity.
Qed.

Lemma path_prism_middle_inner n i x (p : @path_from C n x) :
  i < n ->
  @path_inner_face D n i (fobj F x) (path_prism_from n i x p) =
    @path_inner_face D n i (fobj F x) (path_prism_from n (S i) x p).
Proof.
  revert i x p. induction n as [|n IH]; intros i x p hi.
  - lia.
  - destruct p as [y [f q]]. destruct i as [|i].
    + simpl. rewrite path_prism_from_zero. simpl.
      rewrite (naturality alpha f). reflexivity.
    + simpl. rewrite IH by lia. reflexivity.
Qed.

Lemma path_prism_middle_face n i (p : @path C n) :
  i < n ->
  @path_face D n (S i) (path_prism n i p) =
    @path_face D n (S i) (path_prism n (S i) p).
Proof.
  intros hi. destruct p as [x q].
  unfold path_prism, path_face, path_remove_inner.
  rewrite path_prism_middle_inner by exact hi. reflexivity.
Qed.

Lemma path_prism_left_inner n i j x (p : @path_from C (S n) x) :
  i <= n -> j < i ->
  @path_inner_face D (S n) j (fobj F x) (path_prism_from (S n) (S i) x p) =
    path_prism_from n i x (@path_inner_face C n j x p).
Proof.
  revert i j x p. induction n as [|n IH]; intros i j x p hi hj.
  - lia.
  - destruct i as [|i]; [lia|].
    destruct p as [y [f q]]. destruct j as [|j].
    + destruct q as [z [g r]]. simpl.
      rewrite fmap_compose. reflexivity.
    + simpl. f_equal. f_equal. apply IH; lia.
Qed.

Lemma path_prism_left_face n i j (p : @path C (S n)) :
  i <= n -> j <= i ->
  @path_face D (S n) j (path_prism (S n) (S i) p) =
    path_prism n i (@path_face C n j p).
Proof.
  intros hi hj. destruct j as [|j].
  - destruct p as [x [y [f q]]]. reflexivity.
  - destruct p as [x q]. unfold path_prism, path_face, path_remove_inner.
    rewrite path_prism_left_inner by lia. reflexivity.
Qed.

Lemma path_prism_right_inner n i j x (p : @path_from C (S n) x) :
  i <= j -> j <= n ->
  @path_inner_face D (S n) (S j) (fobj F x) (path_prism_from (S n) i x p) =
    path_prism_from n i x (@path_inner_face C n j x p).
Proof.
  revert i j x p. induction n as [|n IH]; intros i j x p hi hj.
  - assert (i = 0) by lia. assert (j = 0) by lia. subst i j.
    destruct p as [y [f q]]. reflexivity.
  - destruct i as [|i].
    + rewrite !path_prism_from_zero. simpl.
      f_equal. f_equal. symmetry.
      exact (@path_map_inner_face C D G (S n) j x p).
    + destruct j as [|j]; [lia|].
      destruct p as [y [f q]]. simpl. f_equal. f_equal.
      apply (IH i j y q); lia.
Qed.

Lemma path_prism_right_face n i j (p : @path C (S n)) :
  i <= j -> j <= n ->
  @path_face D (S n) (S (S j)) (path_prism (S n) i p) =
    path_prism n i (@path_face C n (S j) p).
Proof.
  intros hi hj. destruct p as [x q]. unfold path_prism, path_face, path_remove_inner.
  rewrite path_prism_right_inner by assumption. reflexivity.
Qed.

End Prism.
Arguments path_prism_from {C D F G} alpha n i x p.
Arguments path_prism {C D F G} alpha n i p.
End DPCategoryBarPrism.
