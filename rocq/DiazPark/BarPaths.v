From Stdlib Require Import Arith.PeanoNat.
From DiazPark Require Import Category.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Composable-arrow chains and the inner faces of the ordinary category bar.
    This is pure category theory; no finiteness or module structure is used. *)
Module DiazParkBarPaths.

Section Paths.
Variable C : category.

Fixpoint path_from (n : nat) (x : C) : Type :=
  match n with
  | 0 => unit
  | S k => {y : C & (hom C x y * path_from k y)%type}
  end.

Arguments path_from _ _ : clear implicits.

Definition path (n : nat) := {x : C & path_from n x}.

Definition path_source (n : nat) (p : path n) : C := projT1 p.

(** Index i removes vertex i+1.  At the final vertex this drops the final
    arrow; otherwise it composes the two adjacent arrows.  Values outside the
    valid range have a harmless total extension, never used in bar identities. *)
Fixpoint path_inner_face (n : nat) :
    forall i x, path_from (S n) x -> path_from n x :=
  match n as k return forall i x, path_from (S k) x -> path_from k x with
  | 0 => fun _ _ _ => tt
  | S k => fun i x p =>
      match p with
      | existT _ y (f, q) =>
          match i with
          | 0 =>
              match q with
              | existT _ z (g, r) => existT _ z (compose f g, r)
              end
          | S j => existT _ y (f, @path_inner_face k j y q)
          end
      end
  end.

Arguments path_inner_face _ _ _ _ : clear implicits.

Lemma path_inner_faces n i j x (p : path_from (S (S n)) x) :
  i <= j -> j <= n ->
  path_inner_face n j x (path_inner_face (S n) i x p) =
    path_inner_face n i x (path_inner_face (S n) (S j) x p).
Proof.
  revert i j x p.
  induction n as [|n IH]; intros i j x p hij hj.
  - reflexivity.
  - destruct i as [|i], j as [|j].
    + destruct p as [y [f q]].
      destruct q as [z [g r]].
      destruct r as [w [h s]].
      simpl. rewrite compose_assoc. reflexivity.
    + destruct p as [y [f q]].
      destruct q as [z [g r]].
      reflexivity.
    + inversion hij.
    + destruct p as [y [f q]].
      change (existT (fun z => (hom C x z * path_from n z)%type)
        y (f, path_inner_face n j y (path_inner_face (S n) i y q)) =
        existT (fun z => (hom C x z * path_from n z)%type)
        y (f, path_inner_face n i y (path_inner_face (S n) (S j) y q))).
      rewrite (IH i j y q (proj2 (Nat.succ_le_mono _ _) hij)
        (proj2 (Nat.succ_le_mono _ _) hj)). reflexivity.
Qed.

Definition path_drop_first n (p : path (S n)) : path n :=
  match p with
  | existT _ x q =>
      match q with
      | existT _ y (_, r) => existT _ y r
      end
  end.

Definition path_remove_inner n i (p : path (S n)) : path n :=
  match p with
  | existT _ x q => existT _ x (path_inner_face n i x q)
  end.

Arguments path_drop_first _ _ : clear implicits.
Arguments path_remove_inner _ _ _ : clear implicits.

Lemma path_remove_inner_source n i (p : path (S n)) :
  path_source (path_remove_inner n i p) = path_source p.
Proof. destruct p. reflexivity. Qed.

Definition path_face n i (p : path (S n)) : path n :=
  match i with
  | 0 => path_drop_first n p
  | S j => path_remove_inner n j p
  end.

Arguments path_face _ _ _ : clear implicits.

(** All ordinary simplicial face identities, including the face that changes
    the source object.  The displayed bounds are the actual valid indices. *)
Lemma path_faces n i j (p : path (S (S n))) :
  i <= j -> j <= S n ->
  path_face n j (path_face (S n) i p) =
    path_face n i (path_face (S n) (S j) p).
Proof.
  intros hij hj. destruct i as [|i], j as [|j].
  - destruct p as [x [y [f [z [g q]]]]]. reflexivity.
  - destruct p as [x [y [f q]]]. reflexivity.
  - inversion hij.
  - destruct p as [x q]. unfold path_face, path_remove_inner.
    rewrite (path_inner_faces q (proj2 (Nat.succ_le_mono _ _) hij)
      (proj2 (Nat.succ_le_mono _ _) hj)). reflexivity.
Qed.

Definition path_insert_identity n (p : path n) : path (S n) :=
  match p with
  | existT _ x q => existT _ x (existT _ x (identity x, q))
  end.

Arguments path_insert_identity _ _ : clear implicits.

Lemma path_drop_insert_identity n (p : path n) :
  path_drop_first n (path_insert_identity n p) = p.
Proof. destruct p. reflexivity. Qed.

Lemma path_first_inner_insert_identity n (p : path (S n)) :
  path_remove_inner (S n) 0 (path_insert_identity (S n) p) = p.
Proof.
  destruct p as [x [y [f q]]].
  simpl. rewrite compose_id_left. reflexivity.
Qed.

End Paths.
End DiazParkBarPaths.
