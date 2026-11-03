(** Actual first-quadrant downward bicomplexes with commuting unsigned maps. *)
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Module DPFirstQuadrantChain.
Section Bicomplex.
Variable R : pzRingType.
Record bicomplex := Bicomplex {
  bicomplex_term : nat -> nat -> lmodType R;
  horizontal : forall p q, {linear bicomplex_term p.+1 q -> bicomplex_term p q};
  vertical : forall p q, {linear bicomplex_term p q.+1 -> bicomplex_term p q};
  horizontal_squared : forall p q x, horizontal p q (horizontal p.+1 q x) = 0;
  vertical_squared : forall p q x, vertical p q (vertical p q.+1 x) = 0;
  horizontal_vertical : forall p q x,
    horizontal p q (vertical p.+1 q x) = vertical p q (horizontal p q.+1 x)
}.
Record bicomplex_map (K L : bicomplex) := BicomplexMap {
  bicomplex_map_at : forall p q, {linear bicomplex_term K p q -> bicomplex_term L p q};
  bicomplex_map_horizontal : forall p q x,
    horizontal L p q (bicomplex_map_at p.+1 q x) = bicomplex_map_at p q (horizontal K p q x);
  bicomplex_map_vertical : forall p q x,
    vertical L p q (bicomplex_map_at p q.+1 x) = bicomplex_map_at p q (vertical K p q x)
}.
End Bicomplex.
End DPFirstQuadrantChain.
