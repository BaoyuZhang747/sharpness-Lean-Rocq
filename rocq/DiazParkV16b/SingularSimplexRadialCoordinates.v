(** Actual radial projection of a punctured standard simplex onto its boundary. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazParkV16b Require Import TopologicalSimplexBasic TopologicalSimplexCompact
  SingularSubdivisionGeometryBarycenter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory DPTopologicalSimplex
  DPTopologicalSimplexCompact DPSingularSubdivisionBarycenter.
Local Open Scope ring_scope.

Module DPSingularSimplexRadialCoordinates.
Section Coordinates.
Variable Real : realType.

Definition coordinate_minimum {n} (x : simplex Real n) : Real :=
  \big[Order.min/1]_i coordinate x i.

Lemma coordinate_minimum_ge0 {n} (x : simplex Real n) : 0 <= coordinate_minimum x.
Proof. apply: le_bigmin => // i _; exact: coordinate_ge0. Qed.

Lemma coordinate_minimum_le {n} (x : simplex Real n) i :
  coordinate_minimum x <= coordinate x i.
Proof. exact: bigmin_le. Qed.

Lemma coordinate_minimum_attained {n} (x : simplex Real n) :
  exists i, coordinate_minimum x = coordinate x i.
Proof.
exists [arg min_(i < ord0) coordinate x i]%O.
apply: bigmin_eq_arg => // i _; exact: coordinate_le1.
Qed.

Definition radial_gap {n} (x : simplex Real n) : Real :=
  1 - n.+1%:R * coordinate_minimum x.

Lemma radial_gap_sum {n} (x : simplex Real n) :
  radial_gap x = \sum_i (coordinate x i - coordinate_minimum x).
Proof.
rewrite /radial_gap sumrB coordinate_sum sumr_const card_ord.
by rewrite mulr_natl.
Qed.

Lemma radial_gap_ge0 {n} (x : simplex Real n) : 0 <= radial_gap x.
Proof.
rewrite radial_gap_sum; apply: sumr_ge0 => i _.
by rewrite subr_ge0; exact: coordinate_minimum_le.
Qed.

Lemma radial_gap_zero_uniform {n} (x : simplex Real n) :
  radial_gap x = 0 -> x = uniform_simplex Real n.
Proof.
move=> hx.
have hp i : 0 <= coordinate x i - coordinate_minimum x.
  by rewrite subr_ge0; exact: coordinate_minimum_le.
have hall : forall i : 'I_n.+1, coordinate x i - coordinate_minimum x = 0.
  have hs : \sum_i (coordinate x i - coordinate_minimum x) = 0 by rewrite -radial_gap_sum hx.
  move=> i; exact (@psumr_eq0P [the numDomainType of (Real : Type)] [the finType of 'I_n.+1] predT (fun j => coordinate x j - coordinate_minimum x) (fun j _ => hp j) hs i isT).
have he i : coordinate x i = coordinate_minimum x := subr0_eq (hall i).
have hs := coordinate_sum x.
have hsum : \sum_i coordinate x i = \sum_(i : 'I_n.+1) coordinate_minimum x.
  apply eq_bigr => i _; exact: he.
rewrite hsum sumr_const card_ord -mulr_natl in hs.
have hn : (n.+1%:R : Real) != 0 by rewrite pnatr_eq0.
have hm : coordinate_minimum x = (n.+1%:R : Real)^-1.
  apply: (mulfI hn); by rewrite hs mulfV.
apply simplex_ext => i; by rewrite he hm uniform_simplex_coordinate.
Qed.

Lemma radial_gap_pos {n} (x : simplex Real n) (hx : x <> uniform_simplex Real n) :
  0 < radial_gap x.
Proof.
rewrite lt0r radial_gap_ge0 andbT.
apply/eqP => h; exact: hx (radial_gap_zero_uniform h).
Qed.

Definition radial_vector {n} (x : simplex Real n) : 'rV[Real]_n.+1 :=
  \row_i ((coordinate x i - coordinate_minimum x) / radial_gap x).

Lemma radial_vector_in {n} (x : simplex Real n) (hx : x <> uniform_simplex Real n) :
  @simplex_set Real n (radial_vector x).
Proof.
split.
- move=> i; rewrite /radial_vector mxE.
  apply: divr_ge0; [by rewrite subr_ge0; exact: coordinate_minimum_le | exact: ltW (radial_gap_pos hx)].
- under eq_bigr do rewrite /radial_vector mxE.
  rewrite -mulr_suml -radial_gap_sum divff //.
  apply/eqP => e; have hp := radial_gap_pos hx; by rewrite e ltxx in hp.
Qed.

Definition radial_projection {n} (x : simplex Real n) (hx : x <> uniform_simplex Real n) : simplex Real n :=
  simplex_of_vector (radial_vector_in hx).

Lemma radial_projection_coordinate {n} (x : simplex Real n) (hx : x <> uniform_simplex Real n) i :
  coordinate (radial_projection hx) i = (coordinate x i - coordinate_minimum x) / radial_gap x.
Proof. by rewrite /radial_projection simplex_of_vector_at /radial_vector mxE. Qed.

Theorem radial_projection_boundary {n} (x : simplex Real n) (hx : x <> uniform_simplex Real n) :
  @boundary_set Real n (radial_projection hx).
Proof.
have [i hi] := coordinate_minimum_attained x; exists i.
by rewrite radial_projection_coordinate hi subrr mul0r.
Qed.

Lemma boundary_coordinate_minimum_zero {n} (x : simplex Real n) (hx : @boundary_set Real n x) :
  coordinate_minimum x = 0.
Proof.
case: hx => i hi; apply/eqP; rewrite eq_le coordinate_minimum_ge0 andbT.
by have := coordinate_minimum_le x i; rewrite hi.
Qed.

Theorem radial_projection_fixes_boundary {n} (x : simplex Real n)
    (hx : x <> uniform_simplex Real n) (hb : @boundary_set Real n x) : radial_projection hx = x.
Proof.
apply simplex_ext => i; rewrite radial_projection_coordinate /radial_gap
  (boundary_coordinate_minimum_zero hb) mulr0 !subr0 divr1; reflexivity.
Qed.

Lemma boundary_not_uniform {n} (x : simplex Real n) (hx : @boundary_set Real n x) :
  x <> uniform_simplex Real n.
Proof.
move=> e; case: hx => i hi; rewrite e uniform_simplex_coordinate in hi.
move: hi => /eqP; by rewrite invr_eq0 pnatr_eq0.
Qed.

Lemma punctured_zero_empty (x : simplex Real 0) : x <> uniform_simplex Real 0 -> False.
Proof. move=> h; apply h; exact: simplex_zero_unique. Qed.

End Coordinates.
End DPSingularSimplexRadialCoordinates.








