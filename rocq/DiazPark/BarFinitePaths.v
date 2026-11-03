From HB Require Import structures.
From mathcomp Require Import all_boot.
From DiazPark Require Import Category CategoryFinite BarPaths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkBarPaths.

(** An actual finite indexing type covering all composable paths.  The bar
    itself still uses its original unrestricted path type. *)
Section FinitePaths.
Variable C : finite_category.

Fixpoint finite_path_from (n : nat) (x : fc_object C) : finType :=
  match n with
  | 0 => [the finType of (unit : Type)]
  | S k => [the finType of {y : fc_object C &
      [the finType of (fc_hom C x y * finite_path_from k y)%type]}]
  end.

Fixpoint finite_path_decode (n : nat) (x : fc_object C) :
    finite_path_from n x -> path_from (C := fc_category C) n x :=
  match n as k return finite_path_from k x -> path_from (C := fc_category C) k x with
  | 0 => fun _ => tt
  | S k => fun i => match i with existT y (f,q) =>
      existT _ y (f, @finite_path_decode k y q) end
  end.

Lemma finite_path_decode_surjective n x (p : path_from (C := fc_category C) n x) :
    exists i, finite_path_decode i = p.
Proof.
elim: n x p => [x []|n ih x [y [f q]]].
- by exists tt.
- have [j hj] := ih y q; exists (existT _ y (f,j)); by rewrite /= hj.
Qed.

Definition finite_path (n : nat) : finType :=
  [the finType of {x : fc_object C & finite_path_from n x}].

Definition finite_path_start n (i : finite_path n) : fc_object C := projT1 i.
Definition finite_path_tail n (i : finite_path n) :
    path_from (C := fc_category C) n (finite_path_start i) :=
  match i with existT x q => finite_path_decode q end.

End FinitePaths.

