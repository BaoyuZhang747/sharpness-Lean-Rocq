(** Under cumulative products, the actual bar differential is vertex deletion. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category BarPaths BarResolutionTerms BarResolutionContraction.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyHomogeneousPaths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomology DPGroupCohomologyHomogeneousPaths DiazParkBarPaths
  DiazParkBarResolutionTerms DiazParkBarResolutionContraction.
Local Open Scope group_scope.

Module DPGroupCohomologyHomogeneousFaces.
Section Faces.
Variable G : finGroupType.

Fixpoint delete_vertex (n i : nat) : power G n.+1 -> power G n :=
  match n return power G n.+1 -> power G n with
  | 0 => fun _ => tt
  | k.+1 => fun v =>
      match i with
      | 0 => v.2
      | j.+1 => (v.1, @delete_vertex k j v.2)
      end
  end.

Arguments delete_vertex n i _ : clear implicits.

Lemma path_to_vertices_face n i b x
    (p : @path_from (group_category G) n.+1 x) :
  path_to_vertices n b x (@path_inner_face (group_category G) n i x p) =
    delete_vertex n i (path_to_vertices n.+1 b x p).
Proof.
elim: n i b x p => [|n IH] i b x p; first reflexivity.
case: p => y [f q]; case: i => [|i].
- case: q => z [g r]; by rewrite /= mulgA.
- by rewrite /= IH.
Qed.

Lemma delete_vertex_translate n i a (v : power G n.+1) :
  delete_vertex n i (left_translate n.+1 a v) =
    left_translate n a (delete_vertex n i v).
Proof.
elim: n i v => [|n IH] i v; first reflexivity.
case: v => b v; case: i => [|i]; first reflexivity.
by rewrite /= IH.
Qed.

Lemma homogeneous_face n i x (p : @path_from (group_category G) n.+2 x) :
  resolution_generator_to_homogeneous (@path_inner_face (group_category G) n.+1 i x p) =
    delete_vertex n.+1 i (resolution_generator_to_homogeneous p).
Proof. exact: path_to_vertices_face. Qed.

Definition insert_vertex n (v : power G n) : power G n.+1 := (1, v).

Arguments insert_vertex n v : clear implicits.

Lemma homogeneous_insert n x (p : @path_from (group_category G) n.+1 x) :
  resolution_generator_to_homogeneous (resolution_insert p) =
    insert_vertex n.+1 (resolution_generator_to_homogeneous p).
Proof.
change (((1 : G) * 1, path_to_vertices n.+1 (1 * 1) x p) =
  (1, path_to_vertices n.+1 1 x p)).
by rewrite mulg1.
Qed.

Lemma delete_insert_zero n (v : power G n.+1) :
  delete_vertex n.+1 0 (insert_vertex n.+1 v) = v.
Proof. reflexivity. Qed.

Lemma delete_insert_succ n i (v : power G n.+1) :
  delete_vertex n.+1 i.+1 (insert_vertex n.+1 v) =
    insert_vertex n (delete_vertex n i v).
Proof. reflexivity. Qed.

End Faces.
Arguments delete_vertex {G} n i _.
Arguments insert_vertex {G} n v.
End DPGroupCohomologyHomogeneousFaces.
