From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators
  SimplexCategoryIdentities SimplicialSet.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialOperators.
Import DPSimplexCategory DPSimplexOperators DPSimplexIdentities DPSimplicialSet.

Definition face (X : simplicial_set) n (i : 'I_n.+2) :
  simplex X n.+1 -> simplex X n := simplex_map X (coface i).

Definition degeneracy (X : simplicial_set) n (i : 'I_n.+1) :
  simplex X n -> simplex X n.+1 := simplex_map X (codegeneracy i).

Arguments face _ {_} _ _.
Arguments degeneracy _ {_} _ _.

Lemma face_face (X : simplicial_set) n (i j : 'I_n.+2)
    (x : simplex X n.+2) : (i <= j)%N ->
  face X j (face X (vertex_widen i) x) =
    face X i (face X (vertex_successor j) x).
Proof.
  intro hij. unfold face. rewrite <- !simplex_map_compose.
  rewrite (coface_coface hij). reflexivity.
Qed.

Lemma degeneracy_degeneracy (X : simplicial_set) n (i j : 'I_n.+1)
    (x : simplex X n) : (i <= j)%N ->
  degeneracy X (vertex_successor j) (degeneracy X i x) =
    degeneracy X (vertex_widen i) (degeneracy X j x).
Proof.
  intro hij. unfold degeneracy. rewrite <- !simplex_map_compose.
  rewrite (codegeneracy_codegeneracy hij). reflexivity.
Qed.

Lemma face_degeneracy_same (X : simplicial_set) n (i : 'I_n.+1)
    (x : simplex X n) : face X (vertex_widen i) (degeneracy X i x) = x.
Proof.
  unfold face, degeneracy. rewrite <- simplex_map_compose.
  rewrite coface_codegeneracy_same. apply simplex_map_identity.
Qed.

Lemma face_degeneracy_successor (X : simplicial_set) n (i : 'I_n.+1)
    (x : simplex X n) : face X (vertex_successor i) (degeneracy X i x) = x.
Proof.
  unfold face, degeneracy. rewrite <- simplex_map_compose.
  rewrite coface_codegeneracy_successor. apply simplex_map_identity.
Qed.

Lemma face_degeneracy_lt (X : simplicial_set) n (i : 'I_n.+2) (j : 'I_n.+1)
    (x : simplex X n.+1) : (i <= j)%N ->
  face X (vertex_widen i) (degeneracy X (vertex_successor j) x) =
    degeneracy X j (face X i x).
Proof.
  intro hij. unfold face, degeneracy. rewrite <- !simplex_map_compose.
  rewrite (coface_codegeneracy_lt hij). reflexivity.
Qed.

Lemma face_degeneracy_gt (X : simplicial_set) n (i : 'I_n.+1) (j : 'I_n.+2)
    (x : simplex X n.+1) : (i < j)%N ->
  face X (vertex_successor j) (degeneracy X (vertex_widen i) x) =
    degeneracy X i (face X j x).
Proof.
  intro hij. unfold face, degeneracy. rewrite <- !simplex_map_compose.
  rewrite (coface_codegeneracy_gt hij). reflexivity.
Qed.

Lemma simplicial_map_face (X Y : simplicial_set) (a : simplicial_map X Y)
    n (i : 'I_n.+2) (x : simplex X n.+1) :
  component a n (face X i x) = face Y i (component a n.+1 x).
Proof. apply simplicial_map_naturality. Qed.

Lemma simplicial_map_degeneracy (X Y : simplicial_set) (a : simplicial_map X Y)
    n (i : 'I_n.+1) (x : simplex X n) :
  component a n.+1 (degeneracy X i x) = degeneracy Y i (component a n x).
Proof. apply simplicial_map_naturality. Qed.

End DPSimplicialOperators.
