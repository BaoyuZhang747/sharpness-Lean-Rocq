(** Actual covariant maps on simplicial chains. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialSetOperators
  SimplicialChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialSet
  DPSimplicialOperators DPSimplicialChains.
Local Open Scope ring_scope.

Module DPSimplicialChainMaps.
Section Maps.
Variable R : pzRingType.
Variables X Y : simplicial_set.
Variable f : simplicial_map X Y.

Definition map_at n : {linear term R X n -> term R Y n} := free_map R (component f n).

Lemma map_at_basis n (x : simplex X n) :
  map_at n (free_basis R x) = free_basis R (component f n x).
Proof. exact: free_map_basis. Qed.

Lemma map_face n i (a : term R X n.+1) :
  face_map R Y n i (map_at n.+1 a) = map_at n (face_map R X n i a).
Proof.
apply (free_lift_ext
  (g := (face_map R Y n i \o map_at n.+1 : {linear _ -> _}))
  (h := (map_at n \o face_map R X n i : {linear _ -> _}))).
move=> x; rewrite /= /map_at /face_map !free_map_basis.
congr (free_basis R _); symmetry; exact: simplicial_map_face.
Qed.

Lemma map_boundary n (a : term R X n.+1) :
  @boundary R Y n (map_at n.+1 a) = map_at n (@boundary R X n a).
Proof.
rewrite /boundary linear_sum; apply eq_bigr => i _.
by rewrite linearZ map_face.
Qed.

Definition chain_map_of : chain_map (chains R X) (chains R Y) :=
  @ChainMap R (chains R X) (chains R Y) map_at map_boundary.

Lemma map_augmentation (a : term R X 0%N) :
  augmentation R Y (map_at 0%N a) = augmentation R X a.
Proof.
apply (free_lift_ext
  (g := (augmentation R Y \o map_at 0%N : {linear _ -> _}))
  (h := augmentation R X)).
move=> x; rewrite /= map_at_basis !augmentation_basis; reflexivity.
Qed.
End Maps.

Section Laws.
Variable R : pzRingType.
Lemma map_identity (X : simplicial_set) n (a : term R X n) :
  map_at R (nat_id X) n a = a.
Proof. exact: free_map_identity. Qed.

Lemma map_composition (X Y Z : simplicial_set)
    (f : simplicial_map X Y) (g : simplicial_map Y Z) n (a : term R X n) :
  map_at R (nat_comp f g) n a = map_at R g n (map_at R f n a).
Proof. exact: free_map_composition. Qed.
End Laws.
End DPSimplicialChainMaps.
