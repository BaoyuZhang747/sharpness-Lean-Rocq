(** Actual first-quadrant cochain bicomplexes with commuting unsigned
    differentials. No exactness or spectral sequence is a field. *)
From mathcomp Require Import all_boot all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPFirstQuadrantCochain.
Section Bicomplex.
Variable R : pzRingType.
Record bicomplex := Bicomplex {
  bicomplex_term : nat -> nat -> lmodType R;
  horizontal : forall p q, {linear bicomplex_term p q -> bicomplex_term p.+1 q};
  vertical : forall p q, {linear bicomplex_term p q -> bicomplex_term p q.+1};
  horizontal_squared : forall p q x, horizontal p.+1 q (horizontal p q x) = 0;
  vertical_squared : forall p q x, vertical p q.+1 (vertical p q x) = 0;
  horizontal_vertical : forall p q x,
    horizontal p q.+1 (vertical p q x) = vertical p.+1 q (horizontal p q x)
}.

Record bicomplex_map (K L : bicomplex) := BicomplexMap {
  bicomplex_map_at : forall p q, {linear bicomplex_term K p q -> bicomplex_term L p q};
  bicomplex_map_horizontal : forall p q x,
    horizontal L p q (bicomplex_map_at p q x) = bicomplex_map_at p.+1 q (horizontal K p q x);
  bicomplex_map_vertical : forall p q x,
    vertical L p q (bicomplex_map_at p q x) = bicomplex_map_at p q.+1 (vertical K p q x)
}.
End Bicomplex.
End DPFirstQuadrantCochain.
