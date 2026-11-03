(** Concrete homogeneous coordinates for the actual group-bar resolution.
    power G n is the recursively defined Cartesian power G^n. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category BarPaths BarResolutionTerms.
From DiazParkV16b Require Import GroupCohomologyBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DiazParkBarPaths DiazParkBarResolutionTerms.
Local Open Scope group_scope.

Module DPGroupCohomologyHomogeneousPaths.
Section Coordinates.
Variable G : finGroupType.

Fixpoint power (n : nat) : Type :=
  match n with 0 => unit | k.+1 => (G * power k)%type end.

Fixpoint left_translate (n : nat) (a : G) : power n -> power n :=
  match n return power n -> power n with
  | 0 => fun _ => tt
  | k.+1 => fun v => (a * v.1, @left_translate k a v.2)
  end.

Arguments left_translate n a _ : clear implicits.

Fixpoint path_to_vertices (n : nat) (b : G) (x : group_category G) :
    @path_from (group_category G) n x -> power n :=
  match n as k return @path_from (group_category G) k x -> power k with
  | 0 => fun _ => tt
  | k.+1 => fun p =>
      match p with existT y (f,q) =>
        (b * f, @path_to_vertices k (b * f) y q)
      end
  end.

Arguments path_to_vertices n b x _ : clear implicits.

Fixpoint vertices_to_path (n : nat) (b : G) (x : group_category G) :
    power n -> @path_from (group_category G) n x :=
  match n as k return power k -> @path_from (group_category G) k x with
  | 0 => fun _ => tt
  | k.+1 => fun v =>
      existT _ tt (b^-1 * v.1, @vertices_to_path k v.1 tt v.2)
  end.

Arguments vertices_to_path n b x _ : clear implicits.

Lemma vertices_path_inverse n b x (p : @path_from (group_category G) n x) :
  vertices_to_path n b x (path_to_vertices n b x p) = p.
Proof.
elim: n b x p => [|n IH] b x p.
- by case: p.
- case: x p => p; case: p => y [f q]; case: y f q => f q.
  rewrite /= !mulgA mulVg mul1g IH; reflexivity.
Qed.

Lemma path_vertices_inverse n b x (v : power n) :
  path_to_vertices n b x (vertices_to_path n b x v) = v.
Proof.
elim: n b x v => [|n IH] b x v.
- by case: v.
- case: v => a v; rewrite /= !mulgA mulgV mul1g IH; reflexivity.
Qed.

Lemma left_translate_identity n (v : power n) : left_translate n 1 v = v.
Proof.
elim: n v => [|n IH] v; first by case: v.
by case: v => a v; rewrite /= mul1g IH.
Qed.

Lemma left_translate_composition n (a b : G) (v : power n) :
  left_translate n (a * b) v = left_translate n a (left_translate n b v).
Proof.
elim: n v => [|n IH] v; first by case: v.
by case: v => c v; rewrite /= mulgA IH.
Qed.

Lemma path_to_vertices_base n (a b : G) x
    (p : @path_from (group_category G) n x) :
  path_to_vertices n (a * b) x p =
    left_translate n a (path_to_vertices n b x p).
Proof.
elim: n a b x p => [|n IH] a b x p; first by case: p.
case: p => y [f q]; rewrite /= mulgA.
by rewrite -(IH a (b * f) y q) mulgA.
Qed.

Definition homogeneous_generator n := power n.+1.

Definition resolution_generator_to_homogeneous n x
    (p : @path_from (group_category G) n.+1 x) : homogeneous_generator n :=
  path_to_vertices n.+1 1 x p.

Definition homogeneous_to_resolution_generator n x
    (v : homogeneous_generator n) : @path_from (group_category G) n.+1 x :=
  vertices_to_path n.+1 1 x v.

Arguments homogeneous_to_resolution_generator n x v : clear implicits.

Lemma resolution_generator_inverse n x
    (p : @path_from (group_category G) n.+1 x) :
  homogeneous_to_resolution_generator n x (resolution_generator_to_homogeneous p) = p.
Proof. exact: vertices_path_inverse. Qed.

Lemma homogeneous_generator_inverse n x (v : homogeneous_generator n) :
  resolution_generator_to_homogeneous (homogeneous_to_resolution_generator n x v) = v.
Proof. exact: path_vertices_inverse. Qed.

Lemma homogeneous_precompose n x y (a : hom (group_category G) x y)
    (p : @path_from (group_category G) n.+1 y) :
  resolution_generator_to_homogeneous (path_precompose a p) =
    left_translate n.+1 a (resolution_generator_to_homogeneous p).
Proof.
case: p => z [f q].
change ((1 * (a * f), path_to_vertices n (1 * (a * f)) z q) =
  (a * (1 * f), left_translate n a (path_to_vertices n (1 * f) z q))).
by rewrite !mul1g path_to_vertices_base.
Qed.

End Coordinates.

Arguments left_translate {G} n a _.
Arguments path_to_vertices {G} n b x _.
Arguments vertices_to_path {G} n b x _.
Arguments homogeneous_to_resolution_generator {G} n x v.

End DPGroupCohomologyHomogeneousPaths.
