(** Actual opposite-category reversal on composable arrow strings. *)
From mathcomp Require Import all_boot boolp.
From DiazPark Require Import Category BarPaths.
From DiazParkV16b Require Import CategoryNerve CategoryNervePaths CategoryNervePathsFaces
  CategoryNerveOpposite SimplicialSetOperators.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkBarPaths DPCategoryNervePathEquivalence DPCategoryNervePathFaces DPCategoryNerveOpposite.

Module DPCategoryStringOppositePaths.
Section Paths.
Variable C : category.

Definition reverse_path n (p : @path C n) : @path (opposite C) n :=
  nerve_path (reverse_nerve (path_nerve p)).

Definition unreverse_path n (p : @path (opposite C) n) : @path C n :=
  nerve_path (unreverse_nerve (path_nerve p)).

Lemma reverse_path_inverse n (p : @path C n) : unreverse_path (reverse_path p) = p.
Proof.
by rewrite /unreverse_path /reverse_path path_nerve_path reverse_nerve_inverse nerve_path_nerve.
Qed.

Lemma unreverse_path_inverse n (p : @path (opposite C) n) : reverse_path (unreverse_path p) = p.
Proof.
by rewrite /unreverse_path /reverse_path path_nerve_path unreverse_nerve_inverse nerve_path_nerve.
Qed.

Lemma reverse_path_face n (i : 'I_n.+2) (p : @path C n.+1) :
  reverse_path (@path_face C n (val i) p) =
  @path_face (opposite C) n (val (rev_ord i)) (reverse_path p).
Proof.
by rewrite /reverse_path path_nerve_face reverse_nerve_face nerve_path_face.
Qed.

Lemma unreverse_path_face n (i : 'I_n.+2) (p : @path (opposite C) n.+1) :
  unreverse_path (@path_face (opposite C) n (val i) p) =
  @path_face C n (val (rev_ord i)) (unreverse_path p).
Proof.
by rewrite /unreverse_path path_nerve_face unreverse_nerve_face nerve_path_face.
Qed.
End Paths.
End DPCategoryStringOppositePaths.
