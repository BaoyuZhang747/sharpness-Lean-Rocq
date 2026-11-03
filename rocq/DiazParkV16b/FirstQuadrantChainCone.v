(** The literal columnwise mapping-cone bicomplex. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra.
From DiazParkV16b Require Import ChainComplex ChainMappingCone
  FirstQuadrantChainBicomplex FirstQuadrantChainTotalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainMappingCone DPFirstQuadrantChain
  DPFirstQuadrantChainTotalMaps.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainCone.
Section Cone.
Variable R : pzRingType.
Variables K L : bicomplex R.
Variable f : bicomplex_map K L.

Definition column_cone_term p q : lmodType R :=
  @cone_term R (vertical_complex K p) (vertical_complex L p) q.
Definition column_cone_horizontal p q : column_cone_term p.+1 q -> column_cone_term p q :=
  match q as k return column_cone_term p.+1 k -> column_cone_term p k with
  | 0%N => horizontal L p 0%N
  | k.+1 => fun x => (horizontal L p k.+1 x.1, horizontal K p k x.2)
  end.
Arguments column_cone_horizontal p q x : clear implicits.

Lemma column_cone_horizontal_linear p q : linear (column_cone_horizontal p q).
Proof.
case: q=> [|q]; move=> r x y; first exact: linearP.
case: x=> x1 x2; case: y=> y1 y2.
change ((horizontal L p q.+1 (r *: x1+y1), horizontal K p q (r *: x2+y2)) =
 (r *: horizontal L p q.+1 x1+horizontal L p q.+1 y1,
  r *: horizontal K p q x2+horizontal K p q y2)).
by rewrite !linearP.
Qed.
HB.instance Definition _ p q := GRing.isLinear.Build R _ _ _
  (column_cone_horizontal p q) (@column_cone_horizontal_linear p q).

Lemma column_cone_horizontal_squared p q (x : column_cone_term p.+2 q) :
  column_cone_horizontal p q (column_cone_horizontal p.+1 q x) = 0.
Proof.
case: q x=> [|q] x; first exact: horizontal_squared.
case: x=> y z; change
 ((horizontal L p q.+1 (horizontal L p.+1 q.+1 y),
   horizontal K p q (horizontal K p.+1 q z)) = (0,0)).
by rewrite !horizontal_squared.
Qed.

Lemma column_cone_commutes p q (x : column_cone_term p.+1 q.+1) :
  column_cone_horizontal p q (@cone_d R (vertical_complex K p.+1) (vertical_complex L p.+1) (vertical_map f p.+1) q x) =
  @cone_d R (vertical_complex K p) (vertical_complex L p) (vertical_map f p) q (column_cone_horizontal p q.+1 x).
Proof.
case: q x=> [|q] [y z].
- change (horizontal L p 0%N (vertical L p.+1 0%N y+bicomplex_map_at f p.+1 0%N z) =
    vertical L p 0%N (horizontal L p 1%N y)+bicomplex_map_at f p 0%N (horizontal K p 0%N z)).
  by rewrite linearD horizontal_vertical bicomplex_map_horizontal.
- change ((horizontal L p q.+1 (vertical L p.+1 q.+1 y+bicomplex_map_at f p.+1 q.+1 z),
    horizontal K p q (-vertical K p.+1 q z)) =
   (vertical L p q.+1 (horizontal L p q.+2 y)+bicomplex_map_at f p q.+1 (horizontal K p q.+1 z),
    -vertical K p q (horizontal K p q.+1 z))).
  by rewrite linearD linearN !horizontal_vertical bicomplex_map_horizontal.
Qed.

Definition column_cone : bicomplex R :=
  @Bicomplex R column_cone_term
    (fun p q => (column_cone_horizontal p q : {linear _ -> _}))
    (fun p q => (@cone_d R (vertical_complex K p) (vertical_complex L p) (vertical_map f p) q : {linear _ -> _}))
    column_cone_horizontal_squared (fun p q => @cone_d_squared R (vertical_complex K p) (vertical_complex L p) (vertical_map f p) q)
    column_cone_commutes.

Lemma column_cone_vertical p : vertical_complex column_cone p = mapping_cone (vertical_map f p).
Proof. reflexivity. Qed.

End Cone.
End DPFirstQuadrantChainCone.
