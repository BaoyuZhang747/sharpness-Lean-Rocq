(** Alexander--Whitney simplex components and their actual diagonal face formulas. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities
  SimplicialSet SimplicialSetOperators BisimplicialSet BisimplicialAlexanderWhitneyOrdinals.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplexOperators DPSimplexIdentities DPSimplicialSet DPSimplicialOperators
  DPBisimplicialSet DPAlexanderWhitneyOrdinals.

Module DPAlexanderWhitneyFaces.
Definition aw_simplex (X : bisimplicial_set) p q n (h : Nat.add p q = n)
  (x : simplex (diagonal X) n) : bisimplex X p q :=
  bisimplex_map X (front p q n h) (back p q n h) x.
Arguments aw_simplex X p q n h x : clear implicits.

Lemma aw_simplex_natural (X Y : bisimplicial_set) (a : bisimplicial_map X Y)
  p q n h (x : simplex (diagonal X) n) :
  bisimplex_component a p q (aw_simplex X p q n h x) =
  aw_simplex Y p q n h (component (diagonal_map a) n x).
Proof. exact: bisimplex_component_natural. Qed.

Lemma aw_face_early (X : bisimplicial_set) p q n (h : Nat.add p q = n)
  (i : 'I_p.+1) (x : simplex (diagonal X) n.+1) :
  aw_simplex X p q n h (face (diagonal X) (early_index p q n h i) x) =
  horizontal_map X (coface (vertex_widen i)) q
    (aw_simplex X p.+1 q n.+1 (successor_left h) x).
Proof.
rewrite /aw_simplex.
change (bisimplex_map X (front p q n h) (back p q n h)
 (bisimplex_map X (coface (early_index p q n h i)) (coface (early_index p q n h i)) x) =
 horizontal_map X (coface (vertex_widen i)) q
 (bisimplex_map X (front p.+1 q n.+1 (successor_left h)) (back p.+1 q n.+1 (successor_left h)) x)).
rewrite -bisimplex_map_compose front_early back_early.
rewrite -(@bisimplex_map_horizontal X p p.+1 (coface (vertex_widen i)) q).
rewrite -bisimplex_map_compose.
congr (bisimplex_map X _ _ x); apply ordinal_map_ext => k; reflexivity.
Qed.

Lemma aw_face_late (X : bisimplicial_set) p q n (h : Nat.add p q = n)
  (j : 'I_q.+1) (x : simplex (diagonal X) n.+1) :
  aw_simplex X p q n h (face (diagonal X) (late_index p q n h j) x) =
  face (fobj X p) (vertex_successor j)
    (aw_simplex X p q.+1 n.+1 (successor_right h) x).
Proof.
rewrite /aw_simplex.
change (bisimplex_map X (front p q n h) (back p q n h)
 (bisimplex_map X (coface (late_index p q n h j)) (coface (late_index p q n h j)) x) =
 simplex_map (fobj X p) (coface (vertex_successor j))
 (bisimplex_map X (front p q.+1 n.+1 (successor_right h)) (back p q.+1 n.+1 (successor_right h)) x)).
rewrite -bisimplex_map_compose front_late back_late.
rewrite -(@bisimplex_map_vertical X p q q.+1 (coface (vertex_successor j))).
rewrite -bisimplex_map_compose.
congr (bisimplex_map X _ _ x); apply ordinal_map_ext => k; reflexivity.
Qed.

Lemma aw_face_middle (X : bisimplicial_set) p q n (h : Nat.add p q = n)
  (x : simplex (diagonal X) n.+1) :
  horizontal_map X (coface (ord_max : 'I_p.+2)) q
    (aw_simplex X p.+1 q n.+1 (successor_left h) x) =
  face (fobj X p) (ord0 : 'I_q.+2)
    (aw_simplex X p q.+1 n.+1 (successor_right h) x).
Proof.
rewrite /aw_simplex.
rewrite -(@bisimplex_map_horizontal X p p.+1 (coface (ord_max : 'I_p.+2)) q).
change (bisimplex_map X (coface (ord_max : 'I_p.+2)) (ordinal_map_identity q)
 (bisimplex_map X (front p.+1 q n.+1 (successor_left h)) (back p.+1 q n.+1 (successor_left h)) x) =
 simplex_map (fobj X p) (coface (ord0 : 'I_q.+2))
 (bisimplex_map X (front p q.+1 n.+1 (successor_right h)) (back p q.+1 n.+1 (successor_right h)) x)).
rewrite -(@bisimplex_map_vertical X p q q.+1 (coface (ord0 : 'I_q.+2))).
rewrite -!bisimplex_map_compose front_middle back_middle.
congr (bisimplex_map X _ _ x); apply ordinal_map_ext => k; reflexivity.
Qed.
End DPAlexanderWhitneyFaces.
